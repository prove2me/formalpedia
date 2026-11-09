-- Prove2me | Theorems.Thm_ParityDegreeDepth_Main_lemma_3_3
-- name    : ParityDegreeDepth.Main.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T13:23:50.701202+00:00
-- url     : https://prove2.me/theorems/8104b196-0eb2-4637-aee0-a65b7abcba88
-- title:
--   Lemma 3.3 — generic versus binary rank
-- statement:
--   Let $N$ be an arbitrary finite rectangular polynomial matrix over $\mathbb F_2$, in $k$ disjoint blocks of $n$ formal variables each. Suppose every entry is linear and homogeneous in each entire block. Let $R(N)$ be its rank over the fraction field of the formal polynomial ring, and let $M(N)$ be the maximum rank of its evaluations over all binary assignments. Then
--   $$R(N)\le2^kM(N).$$
--
--   This compares generic rank to the best binary evaluation without identifying formal polynomial identities with identities of polynomial functions.
--
--   Differences from the source:
--   - encoding: the vector, polynomial and operational mathematical objects stated with each result → Fin-indexed coordinates and private copies of the explicit shared operational definitions, importing only published definitions; reason: the copied definitions are literal copies of the shared Context item restricted to needed declarations; no unpublished draft import or source instance is assumed
--   - encoding: linear and homogeneous in each variable block, generic and binary evaluated ranks → every supported monomial has total exponent one in each block; rank over the fraction field and a finite maximum of all evaluated ranks; reason: the formal polynomial ring retains independent variables and the block condition is total degree per block
-- source:
--   Shengyu Zhang, STOC 2027 submission #798 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/798.pdf, Lemma 3.3, PDF page 7 / printed page 6.

import Mathlib
import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Definitions.Def_ParityCubes_anfCoeff
import Definitions.Def_KakeyaPolynomialMethods
import Definitions.Def_DetCCHard_Protocol

open scoped BigOperators
noncomputable section

namespace ParityDegreeDepth.Main

private abbrev AnchorRing (F : Type) [CommRing F] (n k : ℕ) := MvPolynomial (Fin k × Fin n) F

private abbrev AnchorField (F : Type) [Field F] (n k : ℕ) := FractionRing (AnchorRing F n k)

private def BlockMultilinear {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing F n k)) : Prop :=
  ∀ i j e, e ∈ (N i j).support → ∀ b : Fin k, ∑ v : Fin n, e (b, v) = 1

private def matrixGenericRank {F : Type} [Field F] {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing F n k)) : ℕ :=
  (N.map (algebraMap (AnchorRing F n k) (AnchorField F n k))).rank

private def matrixBinaryRank {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing (ZMod 2) n k)) : ℕ :=
  Finset.univ.sup fun a : (Fin k × Fin n) → ZMod 2 =>
    (N.map (MvPolynomial.eval a)).rank


/-- lemma 3 3; Zhang, STOC 2027 submission #798.
Private operational context is duplicated to avoid unpublished draft imports. -/
theorem lemma_3_3 {n k m r : ℕ}
    (N : Matrix (Fin m) (Fin r) (AnchorRing (ZMod 2) n k))
    (hN : BlockMultilinear N) : matrixGenericRank N ≤ 2 ^ k * matrixBinaryRank N := by sorry

end ParityDegreeDepth.Main
