-- Prove2me | Theorems.Thm_ShamirLLR_lemma_9_1
-- name    : ShamirLLR.lemma_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:27:04.278343+00:00
-- url     : https://prove2.me/theorems/76e0d2c0-3371-4814-b99b-d6289eacb4a6
-- title:
--   Lemma 9.1 — sharp nonzero coefficient $2|\widehat A(\gamma)|\le M_p$
-- statement:
--   Let $E$ be a finite-dimensional vector space over an odd prime field $\mathbb F_p$ and $A:E\to[0,1]$. For every nonzero $\gamma\in E^*$,
--   $$
--   2\Bigl|\mathbb E_{v\in E}A(v)\,e_p(-\gamma(v))\Bigr|\le M_p=\frac{1}{p\sin(\pi/(2p))}.
--   $$
--   Equality is attained by $A(v)=\mathbf 1_{\gamma(v)\in I}$ whenever $I$ is a cyclic interval of $(p-1)/2$ or $(p+1)/2$ residues.
--
--   This exact extremal coefficient yields the base $2/\pi$ in Proposition 9.2 and Theorem 1.
--
--   Differences from the source:
--   - encoding: cyclic interval of $k$ residues → $\{c,c+1,\dots,c+k-1\}\subseteq\mathbb F_p$; reason: definition of a cyclic interval
-- source:
--   Hwang–Maji–Shkredov–Ye, Local Leakage Resilience of Multiplication-friendly Shamir Secret Sharing (manuscript, 2 Nov 2026; held version, sha256 fcd6871f…), Lemma 9.1, Eq. (72), p.64; $M_p$ on p.63 (PDF pp.65, 64)

import Mathlib
import Definitions.Def_ShamirLLR_finFourier

set_option autoImplicit false

namespace ShamirLLR

/-- **Lemma 9.1 (Sharp nonzero coefficient).** Let `E` be a finite-dimensional vector space over
an odd prime field `𝔽_p` and `A : E → [0, 1]`. For every nonzero `γ ∈ E^*`,
`2 |𝔼_{v ∈ E} A(v) e_p(−γ(v))| ≤ M_p = 1/(p sin(π/(2p)))`. Equality is attained by
`A(v) = 1_{γ(v) ∈ I}` when `I` is a cyclic interval of `(p − 1)/2` or `(p + 1)/2` residues.

Source: Hwang–Maji–Shkredov–Ye, manuscript of 2 Nov 2026 (held version, sha256 fcd6871f…),
Lemma 9.1, Eq. (72), p.64; `M_p` on p.63.

**Formalization Note.** A cyclic interval of `k` residues is `{c, c + 1, …, c + k − 1}`. -/
theorem lemma_9_1 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) {E : Type*} [AddCommGroup E]
    [Module (ZMod p) E] [Fintype E] :
    (∀ A : E → ℝ, (∀ v, 0 ≤ A v ∧ A v ≤ 1) → ∀ γ : Module.Dual (ZMod p) E, γ ≠ 0 →
        2 * ‖finFourier A γ‖ ≤ Mp p) ∧
      ∀ γ : Module.Dual (ZMod p) E, γ ≠ 0 → ∀ (c : ZMod p) (k : ℕ),
        (k = (p - 1) / 2 ∨ k = (p + 1) / 2) →
          2 * ‖finFourier (fun v : E =>
              if γ v ∈ (Finset.range k).image (fun j : ℕ => c + (j : ZMod p)) then (1 : ℝ) else 0)
            γ‖ = Mp p := by sorry

end ShamirLLR
