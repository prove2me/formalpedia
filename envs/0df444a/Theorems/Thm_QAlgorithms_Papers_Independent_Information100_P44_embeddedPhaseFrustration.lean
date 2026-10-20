-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P44_embeddedPhaseFrustration
-- name    : QAlgorithms.Papers.Independent.Information100.P44.embeddedPhaseFrustration
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T11:42:27.967733+00:00
-- url     : https://prove2.me/theorems/8f4331a8-9d14-430a-bdb2-cb3523a8d77b
-- title:
--   Corollary 6: embedding of phase frustration in (g,g,1) blocks
-- statement:
--   For every integer $g\ge1$, there are unit vectors $u,v\in\mathbb C^g$ such that the phase-frustration matrix embeds isometrically, with zero extension, as
--   $$G=\begin{pmatrix}uu^\dagger&-uv^\dagger&u\\-vu^\dagger&vv^\dagger&v\\u^\dagger&v^\dagger&1\end{pmatrix}.$$
--   Precisely, $G=VM_{\rm fr}V^\dagger$ for some $V$ with $V^\dagger V=I_3$. All three two-sector principal blocks, of dimensions $2g,g+1,g+1$, are positive semidefinite and rank one, while $G$ is not positive semidefinite. This extends scalar phase frustration without requiring invertible diagonal corners.
-- source:
--   Limitations on Joint Coherence Transfer in Quantum Thermodynamics, arXiv:2608.11872v1, PDF p. 22, Corollary 6: embedding of phase frustration in (g,g,1) blocks

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- PDF p.22, Corollary 6: zero extension embeds phase frustration in (g,g,1) sectors. -/
theorem embeddedPhaseFrustration (g : ℕ) (hg : 1 ≤ g) :
    ∃ u v : Fin g → ℂ,
      (∑ i, Complex.normSq (u i)) = 1 ∧ (∑ i, Complex.normSq (v i)) = 1 ∧
      (∃ V : Matrix (Fin g ⊕ (Fin g ⊕ Fin 1)) (Fin 3) ℂ,
        Vᴴ * V = 1 ∧ frustrationEmbedding u v = V * frustration * Vᴴ) ∧
      (Matrix.fromBlocks
        (Matrix.vecMulVec u (fun i => conj (u i)))
        (-Matrix.vecMulVec u (fun i => conj (v i)))
        (-Matrix.vecMulVec v (fun i => conj (u i)))
        (Matrix.vecMulVec v (fun i => conj (v i)))).PosSemidef ∧
      (Matrix.fromBlocks
        (Matrix.vecMulVec u (fun i => conj (u i)))
        (-Matrix.vecMulVec u (fun i => conj (v i)))
        (-Matrix.vecMulVec v (fun i => conj (u i)))
        (Matrix.vecMulVec v (fun i => conj (v i)))).rank = 1 ∧
      (Matrix.fromBlocks (Matrix.vecMulVec u (fun i => conj (u i)))
        (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) i => conj (u i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).PosSemidef ∧
      (Matrix.fromBlocks (Matrix.vecMulVec u (fun i => conj (u i)))
        (fun i (_ : Fin 1) => u i) (fun (_ : Fin 1) i => conj (u i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).rank = 1 ∧
      (Matrix.fromBlocks (Matrix.vecMulVec v (fun i => conj (v i)))
        (fun i (_ : Fin 1) => v i) (fun (_ : Fin 1) i => conj (v i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).PosSemidef ∧
      (Matrix.fromBlocks (Matrix.vecMulVec v (fun i => conj (v i)))
        (fun i (_ : Fin 1) => v i) (fun (_ : Fin 1) i => conj (v i))
        (fun (_ _ : Fin 1) => (1 : ℂ))).rank = 1 ∧
      ¬ (frustrationEmbedding u v).PosSemidef := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P44
