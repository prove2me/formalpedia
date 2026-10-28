-- Prove2me | Theorems.Thm_ThresholdTheorem_tvDist_le_malignant_pairs
-- name    : ThresholdTheorem.tvDist_le_malignant_pairs
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T20:19:52.481044+00:00
-- url     : https://prove2.me/theorems/af98a7a1-bb36-488f-8ee0-05b34e62694e
-- title:
--   Union bound: if fault patterns avoiding $B$ are harmless, the noisy error is at most $|B|p^2$
-- statement:
--   **Union bound over malignant pairs.** Let $C'$ be a circuit on $n$ blocks of $b$ qubits, $\mathrm{dec}$ a blockwise decoder, $B$ a finite set of pairs of distinct locations $(t,j)$, and $P$ a function on logical outcomes. Let $N$ be an independent stochastic noise model with fault rate at most $p\le 1$. Suppose that **every deterministic fault pattern with the same fault channels as $N$ which contains no pair of $B$ is harmless**: whenever each location is faulty with probability $0$ or $1$, the fault channels are those of $N$, and no pair in $B$ has both locations faulty, the decoded output distribution equals $P$. Then
--   $$d_{\mathrm{TV}}\big(\mathrm{dec}_*P_{\mathrm{noisy}}(C'),\,P\big)\;\le\;|B|\,p^2 .$$
--
--   Proof idea: by multilinearity of the noisy evolution in the fault probabilities, the noisy state is the mixture, over sets $F$ of faulty locations, of the deterministic fault-pattern states, with weights $\prod_{\ell\in F}q_\ell\prod_{\ell\notin F}(1-q_\ell)$. Patterns containing no pair of $B$ contribute exactly $P$ (in particular $P$, the output of the fault-free pattern, is a probability distribution); every other pattern contributes a probability distribution, at TV distance at most $1$ from $P$. Their total weight is the probability that some pair of $B$ is entirely faulty, which by independence and the union bound is at most $\sum_{(\ell,\ell')\in B}q_\ell q_{\ell'}\le|B|p^2$.
-- source:
--   P. Aliferis, D. Gottesman, J. Preskill, Quantum accuracy threshold for concatenated distance-3 codes, arXiv:quant-ph/0504218, Sec. 5 (level-1 bound: failure probability of an exRec at most the number of malignant pairs times p^2, via independent stochastic noise); Nielsen & Chuang, Quantum Computation and Quantum Information, 10th anniv. ed., Sec. 10.6.1, p. 480 (encoded failure probability at most c p^2 by counting pairs of failure points).

import Mathlib
import Definitions.Def_threshold_theorem_noise_model

open ThresholdTheorem

namespace ThresholdTheorem
theorem tvDist_le_malignant_pairs {n b : ℕ} (dec : (Fin b → Fin 2) → Fin 2)
    (C' : Circuit (Fin n × Fin b)) (B : Finset ((ℕ × ℕ) × (ℕ × ℕ)))
    (hB : ∀ x ∈ B, x.1 ≠ x.2) (P : (Fin n → Fin 2) → ℝ)
    (p : ℝ) (hp : p ≤ 1) (N : NoiseModel p)
    (hgood : ∀ N' : NoiseModel 1, (∀ t j, N'.fault t j = N.fault t j) →
      (∀ t j, N'.prob t j = 0 ∨ N'.prob t j = 1) →
      (∀ x ∈ B, N'.prob x.1.1 x.1.2 = 0 ∨ N'.prob x.2.1 x.2.2 = 0) →
      decodeDist dec (outDist (noisyState N' C')) = P) :
    tvDist (decodeDist dec (outDist (noisyState N C'))) P ≤ B.card * p ^ 2 := by sorry
end ThresholdTheorem
