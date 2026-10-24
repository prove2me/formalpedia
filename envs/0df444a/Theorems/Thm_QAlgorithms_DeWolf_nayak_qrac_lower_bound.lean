-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_nayak_qrac_lower_bound
-- name    : QAlgorithms.DeWolf.nayak_qrac_lower_bound
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-13T17:42:55.002839+00:00
-- url     : https://prove2.me/theorems/3a679e8a-c9ed-4242-8659-a76acd1a47ab
-- title:
--   Nayak: quantum random access codes need (1 - H(p))n qubits
-- statement:
--   This is Nayak's lower bound on the length of quantum random access codes.
--
--   Let $n, m \ge 0$ and let $x \mapsto \rho_x$ assign to every $n$-bit string $x \in \{0,1\}^n$ an $m$-qubit mixed state, i.e. a positive semidefinite $2^m \times 2^m$ matrix $\rho_x$ of trace $1$. Let $p$ be a real number with $\frac12 < p \le 1$. Suppose that for every $i \in [n]$ there is a two-outcome measurement $\{M_i, I - M_i\}$ (with $0 \preceq M_i \preceq I$; outcome $1$ for $M_i$, outcome $0$ for $I-M_i$) that recovers $x_i$ with success probability at least $p$ on average over a uniformly random $x$:
--
--   $$
--   \frac{1}{2^n} \sum_{x \in \{0,1\}^n} \Pr[\text{outcome} = x_i \mid \rho_x] \ge p, \qquad \Pr[1 \mid \rho_x] = \operatorname{Tr}(M_i\rho_x).
--   $$
--
--   Then
--
--   $$
--   m \ge \bigl(1 - H(p)\bigr)\, n, \qquad H(p) = -p\log_2 p - (1-p)\log_2(1-p).
--   $$
--
--   The bound says that quantum random access codes cannot be much shorter than classical ones; it is the information-theoretic engine of the quantum proof of the exponential lower bound for 2-query locally decodable codes.
--
--   **Formalization Note** The binary entropy is Mathlib's natural-log binary entropy divided by $\log 2$. Randomized decoding measurements are covered because every randomized two-outcome measurement is a POVM $\{M_i, I-M_i\}$. The hypothesis $p > 1/2$ is the standing assumption on random access codes (p.141); without it the statement fails ($n=1$, $m=0$, $p=0$).
-- source:
--   Ronald de Wolf, Quantum Computing: Lecture Notes, 27 August 2026, PDF p. 142, §15.2, Theorem 4. https://homepages.cwi.nl/~rdewolf/qcnotes.pdf

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false

namespace QAlgorithms.DeWolf

/-- de Wolf p.142, Theorem 4 (Nayak). If `x ↦ ρ_x` encodes `n`-bit strings into `m`-qubit density
matrices so that for every `i` some two-outcome measurement `{M_i, I − M_i}` recovers `x_i` with
success probability at least `p` averaged over a uniform `x` (`IsQRAC ρ p`), where `1/2 < p ≤ 1`
(the random-access-code assumption of p.141), then `m ≥ (1 − H(p)) n` with `H` the binary entropy
in bits. -/
theorem nayak_qrac_lower_bound {n m : ℕ} (ρ : (Fin n → Bool) → Matrix (Qubits m) (Qubits m) ℂ)
    (p : ℝ) (hp : 1 / 2 < p) (hp1 : p ≤ 1) (hρ : IsQRAC ρ p) :
    (1 - binEntropy2 p) * (n : ℝ) ≤ (m : ℝ) := by
  sorry



end QAlgorithms.DeWolf
