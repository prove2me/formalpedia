-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P22_rowSignatureSectors
-- name    : QAlgorithms.Papers.Independent.Information100.P22.rowSignatureSectors
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T10:03:44.937717+00:00
-- url     : https://prove2.me/theorems/2a44ba25-bb7e-4277-8678-9e8e7e9ab295
-- title:
--   Lemma S5: Row-signature sector criterion
-- statement:
--   Let $m,k\ge1$ and let the columns $W_a$, $a=1,\dots,\eta$, be an actual basis of $K=\ker B^T\subseteq\mathbb F_2^{mk}$. The signature at vertex $v$ is $\sigma(v)=(W_a(v))_a$. Then
--   $$\exists\text{ partition into }k\text{ sectors of size }m\text{ on which every }x\in K\text{ is constant}\iff\forall s\in\mathbb F_2^\eta,\ m\mid|\{v:\sigma(v)=s\}|.$$
--   Sectors are represented by a coordinate bijection. The case $\eta=0$ has one signature class of size $mk$, so is included. No encoder-dependent adjacency condition is imposed by this lemma alone.
-- source:
--   Beyond Maximal Entanglement : Exact Resources for Multiparty Encrypted Quantum Cloning, arXiv:2609.28241v1, PDF p. 33, Lemma S5: Row-signature sector criterion

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P22

namespace QAlgorithms.Papers.Independent.Information100.P22

open scoped ComplexConjugate ComplexOrder Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

local instance {I : Type*} [Fintype I] [DecidableEq I] (G : CutGraph I) :
    Fintype (cutKernel G) := Fintype.ofFinite _

/-- Lemma S5, PDF p.33: W is an actual kernel basis, including eta=0. -/
theorem rowSignatureSectors (m k eta : ℕ) (hm : 1 ≤ m) (hk : 1 ≤ k)
    (B : Matrix (Fin (m*k)) (Fin (m*k)) F2)
    (W : Module.Basis (Fin eta) F2 (LinearMap.ker B.transpose.mulVecLin)) :
    HasConstantSectors (LinearMap.ker B.transpose.mulVecLin) ↔
      ∀ signature : Fin eta → F2,
        m ∣ (Finset.univ.filter fun v => (fun a => (W a).1 v) = signature).card := by sorry

end

end QAlgorithms.Papers.Independent.Information100.P22
