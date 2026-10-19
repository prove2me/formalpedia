-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_graphCutSpectrum
-- name    : QAlgorithms.Papers.Independent.Information100.P22.graphCutSpectrum
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:02:44.557121+00:00
-- url     : https://prove2.me/theorems/e2c91e80-0ff0-4842-9bec-40a79fffff8b
-- title:
--   Lemma S3: Reduced graph-state spectrum and cut kernel
-- statement:
--   Let $\nu\ge1$ and fix an ordered balanced cut of a standard simple graph state. Put $K=\ker B^T$, $r=\operatorname{rank}_{\mathbb F_2}B$, and let $K_S(x)$ be the signed signal stabilizer. Then
--   $$\rho_S=2^{-\nu}\sum_{x\in K}K_S(x)=2^{-r}\Pi_K.$$
--   The normalized stabilizer sum $\Pi_K$ is a self-adjoint projector of rank $2^r$. The reduced density has rank $2^r$ (hence the pure state's Schmidt rank is $2^r$), and $S(\rho_S)=r$ bits. This identifies the complete reduced spectrum from the binary cut.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 29, Lemma S3: Reduced graph-state spectrum and cut kernel

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Lemma S3, PDF p.29: signed expansion, projector, rank, and entropy. -/
theorem graphCutSpectrum (nu : ℕ) (hnu : 1 ≤ nu) (G : CutGraph (Fin nu)) :
    traceRight (pureDensity (graphVector G)) =
      ((2 : ℂ)^nu)⁻¹ • ∑ x : cutKernel G, signalStabilizer G.AS x.1 ∧
    traceRight (pureDensity (graphVector G)) = ((2 : ℂ)^G.B.rank)⁻¹ • graphProjector G ∧
    graphProjector G * graphProjector G = graphProjector G ∧
    (graphProjector G)ᴴ = graphProjector G ∧ (graphProjector G).rank = 2^G.B.rank ∧
    (traceRight (pureDensity (graphVector G))).rank = 2^G.B.rank ∧
    vnEntropy (traceRight (pureDensity (graphVector G))) = G.B.rank := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
