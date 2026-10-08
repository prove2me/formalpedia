-- Prove2me | Theorems.Thm_UncertainPricing_Superrep_lemma_2_15
-- name    : UncertainPricing.Superrep.lemma_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:38.538888+00:00
-- url     : https://prove2.me/theorems/4cd6272f-693d-481b-90cd-2247f5ddf5bd
-- title:
--   Lemma 2.15, p. 10 — ℒ₊ ∩ dom Λ ⊂ ⋂_{P∈P′} L¹(P) and Λ(f) ≥ sup_{P′} E_P f ≥ sup_P E_P f
-- statement:
--   Let $\mathbf P$ be a set of martingale measures on $\Omega$ satisfying $H(\bar\mu)$, let $\mathbf P'$ be the set of martingale measures that do not charge polar sets, and let $\mathcal L_+$ be the functions of $\mathcal L$ that are nonnegative quasi-surely. Then
--   $$\mathcal L_+\cap\operatorname{dom}\Lambda\subset\bigcap_{P\in\mathbf P'}L^1(P),$$
--   and for $f\in\mathcal L_+\cap\operatorname{dom}\Lambda$,
--   $$\Lambda(f)\ge\sup\{E_Pf:P\in\mathbf P'\}\ge\sup\{E_Pf:P\in\mathbf P\}. \tag{3}$$
--
--   This is the easy ("weak duality") half of the pricing formula: the superreplication price dominates the expected payoff under every martingale measure that does not charge polar sets, in particular under every model in $\mathbf P$.
--
--   **Formalization Note.** $\operatorname{dom}\Lambda$ is $\{f\in\mathcal L:\Lambda(f)<+\infty\}$. Integrability is part of the conclusion, so the Bochner integrals in the suprema are genuine expectations. Suprema are in `EReal`.
-- source:
--   Denis & Martini, arXiv:math/0607111v1, Lemma 2.15 and display (3), p. 10

import Mathlib
import Definitions.Def_UncertainPricing_Superrep_Setting

namespace UncertainPricing.Superrep

open MeasureTheory Filter Topology BoundedContinuousFunction

theorem lemma_2_15 (T : ℝ) (hT : 0 < T) (μU : StieltjesFunction ℝ) (hμU : IsDistFn T μU)
    (Ps : Set (Measure (Ω T))) (hPs : ∀ P ∈ Ps, IsMartingaleMeasure P ∧ HypU μU P)
    (f : Ω T → ℝ) (hf : InL Ps f) (hf0 : QS Ps (fun ω => 0 ≤ f ω)) (hfΛ : Lam Ps μU f < ⊤) :
    (∀ P ∈ Pprime Ps, Integrable f P) ∧
      supE (Pprime Ps) f ≤ Lam Ps μU f ∧ supE Ps f ≤ supE (Pprime Ps) f := by sorry

end UncertainPricing.Superrep
