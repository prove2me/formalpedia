-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_directionalLadderAlignment
-- name    : QAlgorithms.Papers.Independent.Information100.P44.directionalLadderAlignment
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:43:29.880095+00:00
-- url     : https://prove2.me/theorems/804e40aa-7903-4f43-8df1-6f41ae448aa7
-- title:
--   Proposition 5: directional PSD alignment in (1,g,1) ladder
-- statement:
--   Let $g\ge2$. In a common directional Gram block of sector sizes $(g,g,1)$, suppose
--   $$G=\begin{pmatrix}A_{01}&F&D\\F^\dagger&A_{12}&E\\D^\dagger&E^\dagger&c\end{pmatrix}\succeq0,\quad A_{01}=uu^\dagger,\quad A_{12}=vv^\dagger,$$
--   where $u,v\in\mathbb C^g$ are nonzero, $D,E\in\mathbb C^g$, and $c\ge0$. Then complex scalars $\alpha,\beta,\lambda$ exist with $D=\alpha u$, $E=\beta v$, and $F=\lambda uv^\dagger$. Equivalently, $D\in\mathbb Cu$, $E\in\mathbb Cv$, $\operatorname{Ran}F\subseteq\mathbb Cu$, and $\operatorname{Ran}F^\dagger\subseteq\mathbb Cv$. The rank-one corners are explicit additional assumptions on selected Gram data. This is an auxiliary positivity constraint and makes no claim that the data alone define a physical channel.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 23, Proposition 5: directional PSD alignment in (1,g,1) ladder

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF pp.23–24, Proposition 5: rank-one directional Gram corners are explicit hypotheses.
No rank-one condition on a whole physical coherence mode is inferred. -/
theorem directionalLadderAlignment {g : ℕ} (hg : 2 ≤ g) (A B F : Mat g)
    (D E u v : Fin g → ℂ) (c : ℝ) (hc : 0 ≤ c) (hu : u ≠ 0) (hv : v ≠ 0)
    (hA : A = pureDensity (WithLp.toLp 2 u))
    (hB : B = pureDensity (WithLp.toLp 2 v))
    (hpos : (ladderGram A B F D E (c : ℂ)).PosSemidef) :
    (∃ alpha beta lambda : ℂ, D = alpha • u ∧ E = beta • v ∧
      F = lambda • Matrix.vecMulVec u (fun i => conj (v i))) ∧
    (∃ alpha : ℂ, D = alpha • u) ∧ (∃ beta : ℂ, E = beta • v) ∧
    Set.range F.mulVec ⊆ {x | ∃ alpha : ℂ, x = alpha • u} ∧
    Set.range (Fᴴ).mulVec ⊆ {x | ∃ beta : ℂ, x = beta • v} := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
