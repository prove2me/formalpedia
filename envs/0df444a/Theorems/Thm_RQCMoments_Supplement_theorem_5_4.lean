-- Prove2me | Theorems.Thm_RQCMoments_Supplement_theorem_5_4
-- name    : RQCMoments.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:50:37.811705+00:00
-- url     : https://prove2.me/theorems/12fcfddd-9389-4526-95ef-8b8b8522622a
-- title:
--   Theorem 5.4 — the perturbed distribution $p_\varepsilon=(1+\varepsilon h)p$ induces an $\varepsilon$-approximate unitary $k$-design
-- statement:
--   Let $\varepsilon\in[0,1]$, let $D>1$, and let $p$ be a distribution on $[0,1]$ whose moments of order up to $2k$ agree with those of $\mathrm{Beta}(1,D-1)$. Let $h:[0,1]\to\mathbb R$ be measurable with
--
--   $$\mathbb E_{X\sim p}[h(X)]=0,\qquad \sup_{x\in[0,1]}|h(x)|\le1,$$
--
--   and define $p_\varepsilon$ by $\mathrm dp_\varepsilon(x)=(1+\varepsilon h(x))\,\mathrm dp(x)$. Then
--
--   1. $p_\varepsilon$ is a probability distribution;
--   2. $\mathbb E_{X\sim p_\varepsilon}[f(X)]=\mathbb E_{X\sim p}[f(X)]+\varepsilon\,\mathbb E_{X\sim p}[h(X)f(X)]$ for every integrable $f$;
--   3. the unitary distribution induced by $p_\varepsilon$ (Definition 5.1) is an $\varepsilon$-approximate unitary $k$-design.
--
--   Perturbing the weights of a moment-matching law by a relative amount $\varepsilon$ keeps the design property with relative error $\varepsilon$; Theorem 5.8 uses this to add the $\Omega(\varepsilon)$ term to its lower bound.
--
--   **Formalization Note** $h$ is a measurable function on $\mathbb R$ whose values matter only on $[0,1]$, where $p$ lives; $p_\varepsilon$ is `p.withDensity` of $1+\varepsilon h$ (nonnegative on $[0,1]$). "Integrable" is $p$-integrable. The three claims are the three conjuncts; the last is `IsStrongDesign μ(p_ε) k k ε` (Remark 2.3).
--
--   Differences from the source:
--
--   - encoding: measurable h : [0,1] → ℝ → measurable h : ℝ → ℝ with |h| ≤ 1 on [0,1]; reason: a measurable function on [0,1] extends by 0; values off [0,1] do not affect p
--   - reading: "for every integrable f" (measure not named) → every p-integrable f; reason: the right-hand side is a p-expectation; p-integrable f are p_ε-integrable since 1 + εh ≤ 2
--   - encoding: dp_ε = (1 + εh) dp → p.withDensity (ENNReal.ofReal (1 + ε h)); reason: the density is nonnegative p-a.e.; same measure
--   - encoding: polynomials f of degree at most 2k in (112) → real polynomials of natDegree ≤ 2k; reason: complex polynomials follow by linearity; same condition
--   - encoding: distribution p on [0,1] → probability measure p on ℝ with p([0,1]ᶜ) = 0; reason: same distributions; the induced measure only uses p on [0,1]
-- source:
--   S.-H. Hung, Random Quantum Circuits Beyond Moment Matching, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.4, (116), p.33 (PDF p.35); Definition 5.1, p.31

import Mathlib
import Definitions.Def_RQCMoments_IsStrongDesign
import Definitions.Def_RQCMoments_porterThomas
import Definitions.Def_RQCMoments_Supplement_inducedMeasure

set_option autoImplicit false

open MeasureTheory

namespace RQCMoments

namespace Supplement

/-- **Theorem 5.4** (Hung, *Random Quantum Circuits Beyond Moment Matching*, arXiv:2610.02135 (held version, sha256 079e7da3…), Theorem 5.4, (116), p.33, PDF p.35).
Let `ε ∈ [0,1]`. Let `p` be a distribution on `[0,1]` whose moments of order up to `2k` agree with
those of `Beta(1, D−1)`. Suppose `h : [0,1] → ℝ` is measurable with `E_{X∼p}[h(X)] = 0` and
`sup_{x∈[0,1]} |h(x)| ≤ 1` (116), and define `dp_ε(x) := (1 + εh(x)) dp(x)`. Then `p_ε` is a
probability distribution, `E_{p_ε}[f] = E_p[f] + ε E_p[h f]` for every integrable `f`, and the unitary
distribution induced by `p_ε` is an `ε`-approximate unitary `k`-design.

**Formalization Note** `D > 1` is the standing assumption of Definition 5.1. `h` is a measurable
function on `ℝ` whose values matter only on `[0,1]` (a measurable function on `[0,1]` extends by `0`).
`p_ε` is `p.withDensity (1 + ε h)`; the density is nonnegative on `[0,1]`, where `p` lives, so
`ENNReal.ofReal` changes nothing `p`-a.e. "Integrable" means `p`-integrable (then `f` is also
`p_ε`-integrable, since `1 + εh ≤ 2`). The three claims of the theorem are the three conjuncts; the
last is `IsStrongDesign μ(p_ε) k k ε` (Remark 2.3). -/
theorem theorem_5_4 (D : ℕ) (hD : 1 < D) (k : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (p : Measure ℝ) [IsProbabilityMeasure p] (hp : p (Set.Icc (0 : ℝ) 1)ᶜ = 0)
    (hmom : ∀ f : Polynomial ℝ, f.natDegree ≤ 2 * k →
      ∫ x, f.eval x ∂p = ∫ x, f.eval x ∂(porterThomas D))
    (h : ℝ → ℝ) (hmeas : Measurable h) (hmean : ∫ x, h x ∂p = 0)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |h x| ≤ 1) :
    let pε : Measure ℝ := p.withDensity (fun x => ENNReal.ofReal (1 + ε * h x))
    IsProbabilityMeasure pε ∧
      (∀ f : ℝ → ℝ, Integrable f p → ∫ x, f x ∂pε = ∫ x, f x ∂p + ε * ∫ x, h x * f x ∂p) ∧
      IsStrongDesign (inducedMeasure D pε) k k ε := by sorry

end Supplement

end RQCMoments
