-- Prove2me | Theorems.Thm_ParamSDO_Transition_domE_interval
-- name    : ParamSDO.Transition.domE_interval
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:19:07.470271+00:00
-- url     : https://prove2.me/theorems/972cc4d4-d886-434b-8ed4-f92877fa0a59
-- title:
--   p. 2, after Assumption 2 — 𝓔 is a non-singleton interval; v is proper and concave on 𝓔 and continuous on int(𝓔)
-- statement:
--   In the setting of the parametric semidefinite pair $(\mathrm P_\epsilon)/(\mathrm D_\epsilon)$ with symmetric data, under Assumptions 1 and 2, let $v(\epsilon)\in\mathbb R\cup\{\pm\infty\}$ be the optimal value of $(\mathrm P_\epsilon)$ and $\mathcal E=\{\epsilon:\ v(\epsilon)>-\infty\}$. Then
--
--   1. $\mathcal E$ is an interval (a convex subset of $\mathbb R$);
--   2. $\mathcal E$ contains at least two points (it is nonempty and not a singleton);
--   3. $v$ is proper on $\mathcal E$: $-\infty<v(\epsilon)<+\infty$ for every $\epsilon\in\mathcal E$;
--   4. $v$ is concave on $\mathcal E$;
--   5. $v$ is continuous on $\operatorname{int}(\mathcal E)$.
--
--   $$
--   \mathcal E\ \text{is an interval with}\ |\mathcal E|\ge2,\qquad v:\mathcal E\to\mathbb R\ \text{concave},\qquad v|_{\operatorname{int}(\mathcal E)}\ \text{continuous}.
--   $$
--
--   This is the basic regularity of the optimal value function on which the analysis of the optimal partition rests.
--
--   **Formalization Note** The paper also asserts that $\mathcal E$ is *closed*. That is false under Assumptions 1–2: with $n=2$, $m=1$, $A^1=\operatorname{diag}(1,0)$, $b=1$, $C=\begin{pmatrix}0&1\\1&1\end{pmatrix}$, $\bar C=\operatorname{diag}(0,1)$ both assumptions hold and $v(\epsilon)=-1/(1+\epsilon)$ for $\epsilon>-1$, $v(-1)=-\infty$, so $\mathcal E=(-1,\infty)$. Closedness is therefore not part of this statement. Since $v$ is finite on $\mathcal E$, concavity and continuity are stated for the real-valued function $\epsilon\mapsto v(\epsilon)$ (Lean: `EReal.toReal` of $v$), which is exact on $\mathcal E$.
-- source:
--   Hauenstein, Mohammad-Nezhad, Tang & Terlaky, On computing the nonlinearity interval in parametric semidefinite optimization, arXiv:1908.10499v3, p. 2, paragraph after Assumption 2 ("closed" omitted: false as printed)

import Mathlib
import Definitions.Def_ParamSDO_Transition_Setting

namespace ParamSDO.Transition

theorem domE_interval {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ)
    (C Cbar : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (hC : C.IsHermitian) (hCbar : Cbar.IsHermitian)
    (h1 : Assumption1 A) (h2 : Assumption2 A b C Cbar) :
    Convex ℝ (domE A b C Cbar) ∧ (domE A b C Cbar).Nontrivial ∧
      (∀ ϵ ∈ domE A b C Cbar, v A b C Cbar ϵ < ⊤) ∧
      ConcaveOn ℝ (domE A b C Cbar) (fun ϵ => (v A b C Cbar ϵ).toReal) ∧
      ContinuousOn (fun ϵ => (v A b C Cbar ϵ).toReal) (interior (domE A b C Cbar)) := by sorry

end ParamSDO.Transition
