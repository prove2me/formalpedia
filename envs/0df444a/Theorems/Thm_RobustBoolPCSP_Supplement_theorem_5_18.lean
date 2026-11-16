-- Prove2me | Theorems.Thm_RobustBoolPCSP_Supplement_theorem_5_18
-- name    : RobustBoolPCSP.Supplement.theorem_5_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:33:11.203705+00:00
-- url     : https://prove2.me/theorems/cac5b39d-23a2-4663-b505-60911aac6566
-- title:
--   Theorem 5.18 (Zero-face estimate for conservative selectors) — $\Pr[\rho(S)\notin W]\le C(t+\sqrt\delta+\delta/t)$
-- statement:
--   Let $|A|=q\ge2$, $r\ge1$, let $\rho$ be a Borel above-average selector, and suppose $(P,W)$ has separating certificates $\omega^b$ for $\rho$ (one for each $b\notin W$). There is a finite constant $C$, depending only on $q$, $r$ and the certificates, such that for every probability distribution $\lambda$ on $A^r$, with $\delta=\lambda(A^r\setminus P)$ and the scores $S$ of (17),
--
--   $$\Pr[\rho(S)\notin W]\le C\Big(t+\sqrt\delta+\frac\delta t\Big)\qquad(0<t\le1),$$
--
--   where $\rho(S)=(\rho(S_1),\dots,\rho(S_r))$.
--
--   This is the local estimate behind the randomized algorithm of Theorem 5.14.
--
--   Differences from the source:
--   - encoding: Borel selector → every fibre {z : ρ z = a} is measurable; reason: equivalent for a map into a finite set
--   - encoding: C depending only on q, r and the certificates → C chosen after A, r and the certificate family ω, before ρ, P, W, λ and t; reason: A is determined up to bijection by q
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), Theorem 5.18, p.39

import Mathlib
import Definitions.Def_RobustBoolPCSP_Supplement_GaussRounding
import Definitions.Def_RobustBoolPCSP_Supplement_ConsSep

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace RobustBoolPCSP.Supplement

open RobustBoolPCSP

/-- **Theorem 5.18 (Zero-face estimate for conservative selectors)**, p.39. Cai, Jiang, Zou, *On Robust Promise CSPs*, STOC 2027 submission (manuscript of 2026-11-03,
sha256 fd1be0d0…).
"Let ρ be a Borel above-average selector, and suppose (P, W) has separating certificates for ρ.
There is a finite constant C, depending only on q, r, and the certificates, such that
P[ρ(S) ∉ W] ≤ C (t + √δ + δ/t) (0 < t ≤ 1), (42) uniformly over all probability distributions λ on
A^r." Setting (p.39): the local rounding model of §5.1 (17), `ρ(S) = (ρ(S_1), …, ρ(S_r))`; throughout
the local analysis "q = |A| ≥ 2 and the relation arity is positive" (p.38).

**Formalization Note.** The certificates are a fixed family `ω b` (used for the tuples `b ∉ W`);
`C` is chosen after `A` (of size `q`), `r` and `ω`, and before `ρ`, `P`, `W`, `λ`, `t`. Borel:
every fibre of `ρ` is measurable. -/
theorem theorem_5_18 {A : Type} [Fintype A] [DecidableEq A] (hq : 2 ≤ Fintype.card A) {r : ℕ}
    (hr : 1 ≤ r) (ω : (Fin r → A) → Fin r → A → ℝ) :
    ∃ C : ℝ, ∀ ρ : (A → ℝ) → A, (∀ a, MeasurableSet {z : A → ℝ | ρ z = a}) → IsAboveAvg ρ →
      ∀ P W : Set (Fin r → A), (∀ b, b ∉ W → IsSepCert ρ P b (ω b)) →
      ∀ lam : (Fin r → A) → ℝ≥0, ∑ x, (lam x : ℝ) = 1 → ∀ t : ℝ, 0 < t → t ≤ 1 →
        gaussLaw lam {z | (fun i => ρ (score lam t z i)) ∉ W} ≤
          ENNReal.ofReal (C * (t + Real.sqrt (defect P lam) + defect P lam / t)) := by sorry

end RobustBoolPCSP.Supplement
