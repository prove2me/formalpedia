-- Prove2me | Theorems.Thm_RelationalReciprocity_Dynamics_lemma_4
-- name    : RelationalReciprocity.Dynamics.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:17:50.245984+00:00
-- url     : https://prove2.me/theorems/766a26a4-7aa9-4750-9412-4b2165191539
-- title:
--   Lemma 4, p. 18 — with (DE) binding, effort falls below first best and the wage rises; positive wage iff η > η̃ < η̄
-- statement:
--   Let $\theta>0$, $\eta>0$ and the standing assumptions hold, let $K>0$ be a dynamic enforcement bound at which (DE) binds (no first-best pair satisfies $b(e,w)\le K$), and let $(e,w)$ be optimal for the period problem with bound $K$. Then there is a multiplier $\lambda>0$ such that $b(e,w)=K$ and either
--   $$
--   \eta^2\theta^3(1+\lambda)>1,\quad w=\frac{(\eta^2\theta^3(1+\lambda)-1)^2}{4\eta^3\theta^3(1+\lambda)^2},\quad e=\frac{1+\eta^2\theta^3(1+\lambda)}{2\eta\theta(1+\lambda)},
--   $$
--   or $\eta^2\theta^3(1+\lambda)\le1$, $w=0$ and $e=\sqrt{\theta/(1+\lambda)}$. Moreover:
--
--   1. for every first-best pair $(e_0,w_0)$, $e<e_0$, and if $\eta>\bar\eta=\sqrt{1/\theta^3}$ then $w>w_0$;
--   2. with $\tilde\eta=\sqrt{1/(\theta^3(1+\lambda))}$ one has $\tilde\eta<\bar\eta$, and $w>0$ if and only if $\eta>\tilde\eta$.
--
--   So a binding enforcement constraint lowers effort below its first-best level, raises the wage when a positive wage is already first-best, and otherwise lowers the reciprocity threshold above which a positive wage is optimal.
--
--   **Formalization Note.** The paper's "period $t<T$" becomes a bound $K>0$: in period $T$ the bound is $0$ and no finite multiplier exists. The multiplier $\lambda$ is the paper's $\lambda_{DE_t}$; the closed forms are those of the proof. The last sentence of Lemma 4 ("$\tilde\eta_t$ is increasing in $\delta$") is not stated. The hypothesis $\eta>0$ is added because the formulas divide by $\eta$.
-- source:
--   Fahn, Reciprocity in Dynamic Employment Relationships, CRC TRR 190 Discussion Paper No. 198 (Nov. 8, 2019), p. 18 (PDF 20), Lemma 4 (without its last sentence); closed forms from its proof, p. 41 (PDF 43)

import Mathlib
import Definitions.Def_RelationalReciprocity_Dynamics_Model

namespace RelationalReciprocity.Dynamics

/-- Lemma 4, p. 18, with the closed forms of its proof, p. 41: if the (DE) constraint with bound
`K > 0` binds, every optimal pair `(e, w)` exhausts the bound and is the KKT point of some
multiplier `λ > 0`; its effort is below first-best effort, its wage is above the first-best wage
when `η > η̄`, and its wage is positive exactly when `η > η̃ = √(1/(θ³(1+λ)))`, where `η̃ < η̄`. -/
theorem lemma_4 (P : Params) (hP : P.Standing) (hη : 0 < P.η) (K : ℝ) (hK : 0 < K)
    (hbind : ¬ DESlack P K) (e w : ℝ) (hopt : IsOptimal P K e w) :
    ∃ lam : ℝ, 0 < lam ∧ bonus P e w = K ∧
      ((1 < P.η ^ 2 * P.θ ^ 3 * (1 + lam) ∧ w = kktWage P lam ∧ e = kktEffort P lam) ∨
        (P.η ^ 2 * P.θ ^ 3 * (1 + lam) ≤ 1 ∧ w = 0 ∧ e = kktEffort0 P lam)) ∧
      (∀ e₀ w₀ : ℝ, IsFirstBest P e₀ w₀ → e < e₀ ∧ (etabar P < P.η → w₀ < w)) ∧
      etatilde P lam < etabar P ∧
      (0 < w ↔ etatilde P lam < P.η) := by sorry

end RelationalReciprocity.Dynamics
