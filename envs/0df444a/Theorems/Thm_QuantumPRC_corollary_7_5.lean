-- Prove2me | Theorems.Thm_QuantumPRC_corollary_7_5
-- name    : QuantumPRC.corollary_7_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:38:13.585136+00:00
-- url     : https://prove2.me/theorems/085de938-37ad-4723-bfa8-7488924d553c
-- title:
--   Corollary 7.5 — under Assumption 5, PRICs robust to every $o(n_{\mathrm P}\log\log n_{\mathrm P}/\log n_{\mathrm P})$-local noise exist
-- statement:
--   There is a constant $\gamma\ge1$ such that the following holds. Let $n_{\mathrm L},n_{\mathrm P}$ be efficient polynomial lengths with $n_{\mathrm P}(\lambda)\ge\gamma\,n_{\mathrm L}(\lambda)$ and $n_{\mathrm P}(\lambda)\ge\lambda^\kappa$ for all $\lambda$, for some constant $\kappa>0$. If Assumption 5 holds, then there is a secret-key code $(\mathsf{KeyGen},\mathrm{Enc},\mathrm{Dec})$ from $n_{\mathrm L}$ to $n_{\mathrm P}$ qubits, with PPT key generation and uniform QPT encoder and decoder, all reading a parameter $1^W$, such that for every function $w:\mathbb N\to\mathbb N$ with
--
--   $$
--   w=o\Big(\frac{n_{\mathrm P}\log\log n_{\mathrm P}}{\log n_{\mathrm P}}\Big),
--   $$
--
--   the code run at $W=\min(w,n_{\mathrm P})$ is a PRIC robust to every $w$-local noise: for every $w$-local noise family $\mathcal E$,
--   $$
--   \big\|\mathbb E_{\mathsf{sk}}(\mathrm{Dec}_{\mathsf{sk}}\circ\mathcal E_\lambda\circ\mathrm{Enc}_{\mathsf{sk}})-\mathrm{id}\big\|_\diamond\le\mathsf{negl}(\lambda),
--   $$
--   and no uniform QPT adversary with oracle access distinguishes $\mathrm{Enc}_{\mathsf{sk}}$ from a Haar-random isometry from $n_{\mathrm L}$ to $n_{\mathrm P}$ qubits with non-negligible advantage.
--
--   This is the main result of the paper: pseudorandom isometric codes at constant rate, robust to local noise of nearly linear weight, from post-quantum LPN or LWE variants.
--
--   Differences from the source:
--   - generalization: n, m (or nL, nP, ℓ, r, m) are polynomials → they are EffPoly lengths: polynomially bounded and computable from 1^λ in polynomial time; reason: every integer-valued polynomial is such a length, so the Lean statement contains the printed one (paper.md decision 2)
--   - encoding: there exists a constant γ > 0 → there exists γ ≥ 1; reason: equivalent: if the statement holds for γ₀ it holds for every larger γ (fewer pairs); γ ≥ 1 gives nL ≤ nP as §4 assumes
--   - reading: for every function w … there exist PRICs → one scheme whose algorithms read 1^{min(w, nP)}; for every such w it is a PRIC at that parameter; reason: the construction depends on w only through this value; composing with a machine for w gives the printed per-w PRICs for every w computable in polynomial time; for arbitrary w it is what the paper's construction supports (paper.md decision 4)
--   - reading: QPT algorithm / QPT adversary (no machine model given) → uniform families of Clifford+T oracle circuits printed by a polynomial-time Turing machine; PPT algorithms are polynomial-time functions of polynomially many fair coins; reason: the paper fixes no model; this one covers adaptive and reference-entangled queries and is used on both sides of every implication (paper.md decision 3)
--   - encoding: Haar measure µ_{nL→nP} on isometries → V = U·ι with U Haar on U(2^{nP}); reason: the realization used on p.69 of the paper
--   - encoding: the adversary A^{(·)}(1^λ) → the λ-th circuit of a uniform family, run on the empty classical input; reason: the index λ carries the same information as the input 1^λ
--   - reading: Assumption 5 as printed (n^ϵ as a dimension, log without a base in items 3–4, Ω(log² n) and Θ(log n), QPT adversaries for Assumptions 1–4) → n^ϵ is ⌊n^ϵ⌋; log is log₂ in items 3–4 (Real.logb 2; ⌈log n⌉ is ⌈Real.logb 2 n⌉₊); Ω/Θ are eventual bounds with natural log over every function g, t; the adversaries are uniform circuit families indexed by the sample number n that read a prefix of the challenge code; reason: the paper fixes neither a log base (§3.1, p.16) nor a rounding of n^ϵ; log₂ is the base of [Lee26]; Ω/Θ are base-free (paper.md decision 8)
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Corollary 7.5, p.42 (informal Theorem 1.1, p.5); Definitions 3.7, 4.3, 4.4; Assumption 5

import Mathlib
import Definitions.Def_QuantumPRC_ChScheme

open Filter Asymptotics

namespace QuantumPRC

/-- **Corollary 7.5** (PRICs from Assumption 5). Hsieh, Yamada, *Quantum Pseudorandom
Error-Correcting Codes*, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d…),
Corollary 7.5, p.42: "There exists a constant `γ > 0` such that the following holds. Let
`nL, nP : ℕ → ℕ` be polynomials satisfying `nP ≥ γ nL` and `nP(λ) ≥ λ^κ` for some constant `κ > 0`. If
Assumption 5 holds, then, for every function `w : ℕ → ℕ` satisfying `w = o(nP log log nP / log nP)`,
there exist PRICs encoding `nL` logical qubits into `nP` physical qubits and robust to any `w`-local
noise."

**Formalization Note.**
* "Polynomials" are `EffPoly` lengths (polynomially bounded, `1^λ ↦ 1^{n(λ)}` polynomial-time); every
  polynomial is one.
* `γ` is taken `≥ 1`; this is equivalent to `γ > 0` (a larger `γ` admits fewer pairs) and gives
  `nL ≤ nP`, as §4 assumes.
* One scheme serves every `w`: its machines read `1^{W(λ)}` with `W = min(w, nP)` (`IsPRICAt`). For
  every `w` computable from `1^λ` in polynomial time this yields the printed per-`w` scheme by
  composing machines; for an arbitrary `w` it is the meaning of "there exist PRICs … for every `w`"
  that the paper's construction supports.
* `nP` may be odd; the paper's construction assumes `nP` even (p.40).
* `log` is `Real.log`; its values for `nP(λ) ≤ 2` are conventions, and `o(·)` ignores them because
  `nP(λ) ≥ λ^κ → ∞`. -/
theorem corollary_7_5 :
    ∃ γ : ℝ, 1 ≤ γ ∧ ∀ nL nP : ℕ → ℕ, EffPoly nL → EffPoly nP →
      (∀ lam, γ * (nL lam : ℝ) ≤ nP lam) →
      (∃ κ : ℝ, 0 < κ ∧ ∀ lam : ℕ, (lam : ℝ) ^ κ ≤ nP lam) →
      Assumption5 →
      ∃ S : ChScheme nL nP, S.Implementable ∧
        ∀ w : ℕ → ℕ,
          (fun lam => (w lam : ℝ)) =o[atTop]
            (fun lam => (nP lam : ℝ) * Real.log (Real.log (nP lam)) / Real.log (nP lam)) →
          S.IsPRICAt w := by sorry

end QuantumPRC
