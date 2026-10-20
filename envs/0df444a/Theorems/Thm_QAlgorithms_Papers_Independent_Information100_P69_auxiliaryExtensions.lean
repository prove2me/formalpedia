-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P69_auxiliaryExtensions
-- name    : QAlgorithms.Papers.Independent.Information100.P69.auxiliaryExtensions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:08:31.456505+00:00
-- url     : https://prove2.me/theorems/43f629e9-6cbb-4b6d-983c-8b7d042706c4
-- title:
--   Comparison with auxiliary extensions
-- statement:
--   Let $N:A\to B$ be CPTP, $\mathcal F$ nonempty compact convex, and $V:A\to B\otimes E$ a fixed Stinespring isometry of $N$. Let $\mathcal G$ consist of all CPTP extensions whose $B$ marginal lies in $\mathcal F$. Write $\beta_\varepsilon=\beta_\varepsilon(N,\mathcal F)$ and $\gamma_u=\beta_u(\operatorname{Ad}_V,\mathcal G)$. For $0<\varepsilon<1$, put $s=\sqrt{1-\varepsilon}$, $r=(1+s)/2$, $\delta=1-r^2$, and $t=(1-s)^2/4$. Then
--   $$0<\delta<1,\quad t>0,\quad t\beta_\varepsilon\le\gamma_\delta,\quad\gamma_\varepsilon\le\beta_\varepsilon.$$
--   These parameters are independent of dimensions. This compares testing with and without auxiliary-output access, without tensor-family hypotheses.
-- source:
--   A Generalized Stein Lemma for Quantum Channels, arXiv:2609.30762v1, PDF p. 28, Lemma 26

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P69

noncomputable section

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Information100.P69

attribute [local instance] Classical.propDecidable Classical.decEq

section Statements

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Lemma 26, testing against all channel extensions, PDF pp.28–29. -/
theorem auxiliaryExtensions [Nonempty A] [Nonempty B] {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
    (N : Superop A B) (hN : IsChannel N) (F : Set (Superop A B)) (hF : CompactConvexChannels F)
    (V : Matrix (B × E) A ℂ) (hV : V.conjTranspose*V = 1) (hNV : N = dilationMap V)
    (eps : ℝ) (heps : 0 < eps) (heps1 : eps < 1) :
    let G : Set (Superop A (B × E)) := {L | IsChannel L ∧ (fun X => QAlgorithms.traceRight (L X)) ∈ F}
    let s := Real.sqrt (1-eps)
    let r := (1+s)/2
    let delta := 1-r^2
    let t := (1-s)^2/4
    0 < delta ∧ delta < 1 ∧ 0 < t ∧ t*beta N F eps ≤ beta (conjSuperop V) G delta ∧
      beta (conjSuperop V) G eps ≤ beta N F eps := by sorry

end Statements

end QAlgorithms.Papers.Independent.Information100.P69

end
