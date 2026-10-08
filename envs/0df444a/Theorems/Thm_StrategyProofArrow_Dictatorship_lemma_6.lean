-- Prove2me | Theorems.Thm_StrategyProofArrow_Dictatorship_lemma_6
-- name    : StrategyProofArrow.Dictatorship.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:17.264977+00:00
-- url     : https://prove2.me/theorems/84816139-031d-4961-8a6d-287c33fa60ff
-- title:
--   Lemma 6 — the choice of a strategy-proof procedure depends only on the ballots' rankings of its range
-- statement:
--   Consider a strict committee $\langle I_n,S_m,v^{nm},T=T_p\rangle$ with $n\ge 2$, $m\ge 3$, $p\ge 1$ and $m\ge p$. If $v^{nm}$ is strategy-proof and two strict ballot sets $C,D\in\rho^n_m$ satisfy $\theta_T(C_i)=\theta_T(D_i)$ for every $i\in I_n$, that is, each $C_i$ and $D_i$ rank the elements of $T$ in the same order, then
--
--   $$v^{nm}(C)=v^{nm}(D).$$
--
--   This is an "independence of irrelevant alternatives" property: alternatives outside the range do not influence the choice. It lets a strategy-proof procedure be viewed as a procedure on the alternatives of its range alone.
--
--   **Formalization Note** $\theta_T(C_i)=\theta_T(D_i)$ is `AgreeOn (range f) (C i) (D i)`: the strict parts of $C_i$ and $D_i$ agree on $T\times T$. The paper states $n\ge 2$; the hypothesis is kept as printed. $m\ge p$ holds automatically (the range is a subset of the alternatives) and is not stated.
-- source:
--   Satterthwaite, Strategy-proofness and Arrow's Conditions, Northwestern Discussion Paper No. 122 (rev. Dec. 12, 1974), Lemma 6, p. 26

import Mathlib
import Definitions.Def_StrategyProofArrow_Dictatorship_Basic

namespace StrategyProofArrow.Dictatorship

open AGT

/-- **Lemma 6** (Satterthwaite, p. 26). For a strict committee with `n ≥ 2`, `m ≥ 3` and
`p ≥ 1` (`m ≥ p` holds automatically), if `f` is strategy-proof and the strict ballot sets `C`,
`D` satisfy `θ_T(C_i) = θ_T(D_i)` for every individual `i`, where `T = T_p` is the range, then
`f C = f D`. -/
theorem lemma_6 {ι A : Type*} [Fintype ι] [Fintype A] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hm : 3 ≤ Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hp : 1 ≤ (range f).ncard)
    (hsp : IncentiveCompatible f)
    (C D : ι → A → A → Prop) (hC : IsPrefProfile C) (hD : IsPrefProfile D)
    (hCD : ∀ i, AgreeOn (range f) (C i) (D i)) :
    f C = f D := by sorry

end StrategyProofArrow.Dictatorship
