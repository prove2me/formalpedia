-- Prove2me | Theorems.Thm_QCQPTightness_ConvHull_lemma_8
-- name    : QCQPTightness.ConvHull.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T17:31:48.955186+00:00
-- url     : https://prove2.me/theorems/2e276d77-e47b-4320-9f8e-733f0c61ff82
-- title:
--   Lemma 8, p. 13 — under Assumption 3, Γ = Γ_e + cone(Γ_r) with polytopes Γ_e, Γ_r, and ℱ(x̂) = ℱ_e(x̂) + cone(ℱ_r(x̂)) when sup_{γ∈Γ} q(γ, x̂) is finite
-- statement:
--   Suppose Assumption 3 holds ($\Gamma$ is polyhedral). Then there are polytopes $\Gamma_e=\mathrm{conv}(E)$ and $\Gamma_r=\mathrm{conv}(R)$, with $E,R\subseteq\mathbb R^m$ finite, such that
--   $$\Gamma=\Gamma_e+\mathrm{cone}(\Gamma_r)$$
--   (Minkowski sum; $\Gamma_r$ may be trivial, giving $\mathrm{cone}(\Gamma_r)=\{0\}$). Moreover, for every $\hat x\in\mathbb R^N$ such that $\sup_{\gamma\in\Gamma}q(\gamma,\hat x)$ is finite,
--   $$\mathcal F(\hat x)=\mathcal F_e(\hat x)+\mathrm{cone}(\mathcal F_r(\hat x)),$$
--   where $\mathcal F_e(\hat x)=\arg\max_{\gamma\in\Gamma_e}q(\gamma,\hat x)$ and $\mathcal F_r(\hat x)=\{\gamma\in\Gamma_r:\ \breve q(\gamma,\hat x)=0\}$, with $\breve q(\gamma,x)=\sum_{i=1}^m\gamma_iq_i(x)$.
--
--   This Minkowski–Weyl splitting of $\Gamma$ and of its maximizing face is what makes the set of extreme constraints in Lemma 7's argument finite.
--
--   **Formalization Note.** The page says "$\mathcal F_r(\hat x)$ is the face of $\Gamma_e$ satisfying $\breve q(\gamma,\hat x)=0$"; the proof and the use in Lemma 7 take it in $\Gamma_r$, which is what is formalized. $\mathrm{cone}(S)$ is the conic hull (`PointedCone.hull`), so $\mathrm{cone}(\emptyset)=\{0\}$. Finiteness of the supremum is expressed as boundedness above of $\{q(\gamma,\hat x):\gamma\in\Gamma\}$. The decomposition $(E,R)$ is chosen once, before $\hat x$.
-- source:
--   arXiv:1911.09195v3, Lemma 8, p. 13 (printed 'face of Γ_e' for ℱ_r read as Γ_r)

import Mathlib
import Definitions.Def_QCQPTightness_ConvHull_QCQP
import Definitions.Def_QCQPTightness_ConvHull_Faces
import Definitions.Def_QCQPTightness_ConvHull_Recession
open Pointwise

namespace QCQPTightness.ConvHull

/-- Lemma 8 (arXiv:1911.09195v3, p. 13). Under Assumption 3, `Γ = Γ_e + cone(Γ_r)` for polytopes
`Γ_e = conv(E)` and `Γ_r = conv(R)` (`E`, `R` finite; `R = ∅` gives `cone(Γ_r) = {0}`), and for every
`x̂` with `sup_{γ∈Γ} q(γ, x̂)` finite, `ℱ(x̂) = ℱ_e(x̂) + cone(ℱ_r(x̂))`, where `ℱ_e(x̂)` is the set
of maximizers of `q(·, x̂)` over `Γ_e` and `ℱ_r(x̂) = {γ ∈ Γ_r : q̆(γ, x̂) = 0}`. The page prints
"the face of Γ_e" for `ℱ_r(x̂)`; the proof and Lemma 7 use `Γ_r`, which is formalized here. -/
theorem lemma_8 {N m : ℕ} (P : QCQP N m) (h3 : P.Assumption3) :
    ∃ E R : Finset (Fin m → ℝ),
      P.Gamma = convexHull ℝ (E : Set (Fin m → ℝ)) +
        (PointedCone.hull ℝ (convexHull ℝ (R : Set (Fin m → ℝ))) : Set (Fin m → ℝ)) ∧
      ∀ x : Fin N → ℝ, BddAbove ((fun γ => P.qγ γ x) '' P.Gamma) →
        P.faceOf x =
          {γ | γ ∈ convexHull ℝ (E : Set (Fin m → ℝ)) ∧
              ∀ γ' ∈ convexHull ℝ (E : Set (Fin m → ℝ)), P.qγ γ' x ≤ P.qγ γ x} +
          (PointedCone.hull ℝ
            {γ | γ ∈ convexHull ℝ (R : Set (Fin m → ℝ)) ∧ P.qBreve γ x = 0} :
            Set (Fin m → ℝ)) := by sorry

end QCQPTightness.ConvHull
