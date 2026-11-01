-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P82_trace_level_sphere_and_tiles
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P82.trace_level_sphere_and_tiles
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:12:09.858171+00:00
-- url     : https://prove2.me/theorems/155b8101-0f0d-4686-9aa0-cddd84716025
-- title:
--   Unnumbered §IV: spherical trace levels and Clifford fundamental tiles
-- statement:
--   All circuits are single-qubit circuits without ancillas or measurements. Products act from right to left. Let $H=i\,2^{-1/2}\begin{pmatrix}1&1\\1&-1\end{pmatrix}$, $T=\operatorname{diag}(e^{-i\pi/8},e^{i\pi/8})$, $S=T^2$, and $C=\langle H,S\rangle\subset\operatorname{PSU}(2)$. The two distinct syllable letters are $a=TH$ and $b=SH$. A normalized word is empty, or ends in $a$ with no adjacent $b$ letters. A canonical word is normalized and its first four syllables, when present, are all $a$. Write $\tau(c)$ for the number of $a$ letters in $c$; Clifford gates have zero charged cost.
--
--   Fix $0<t<2$. Every projective gate of absolute trace $t$ has a unique positive-trace special-unitary representative, parametrized uniquely by $v=(x,y,z)\in S^2$ as
--
--   $$U_t(v)=\frac t2 I+i\sqrt{1-t^2/4}\,(xX+yY+zZ).$$
--
--   Every unit vector gives a special-unitary matrix of trace $t$, and all such matrices arise uniquely. Clifford conjugation becomes the faithful group of 24 orientation-preserving octahedral rotations. The closed spherical triangle with vertices $+X,+Z,(1,1,1)/\sqrt3$ has 24 translates covering $S^2$ with pairwise disjoint relative interiors, and the union of their vertex sets has cardinality 14. These coordinates support the source's secondary geometric search indices.
-- source:
--   A Depth-Optimal Canonical Form for Single-qubit Quantum Circuits, arXiv:1206.3223v1, PDF p. 4, Unnumbered §IV: spherical trace levels and Clifford fundamental tiles

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P82

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakenext100.P82

open scoped BigOperators

local notation "Mat" => Matrix Bool Bool ℂ

/-- Unnumbered §IV, PDF pp.4--5: the nonextreme trace level is a sphere,
Clifford conjugation is the faithful rotational octahedral action, and the stated
triangle has 24 translates with disjoint relative interiors and 14 total vertices. -/
theorem trace_level_sphere_and_tiles (t : ℝ) (ht : 0 < t) (ht2 : t < 2) :
    (∀ U : Mat, U ∈ Matrix.unitaryGroup Bool ℂ → ‖Matrix.trace U‖ = t →
      ∃! V : Mat, V ∈ Matrix.unitaryGroup Bool ℂ ∧ V.det = 1 ∧
        Matrix.trace V = (t : ℂ) ∧ SameGate U V) ∧
    (∀ v ∈ unitSphere,
      sphereGate t v ∈ Matrix.unitaryGroup Bool ℂ ∧
      (sphereGate t v).det = 1 ∧ Matrix.trace (sphereGate t v) = (t : ℂ)) ∧
    (∀ U : Mat, U ∈ Matrix.unitaryGroup Bool ℂ → U.det = 1 →
      Matrix.trace U = (t : ℂ) → ∃! v : BsSphereVector, v ∈ unitSphere ∧ sphereGate t v = U) ∧
    (∀ g : Fin 24, ∀ v ∈ unitSphere,
      (bsCliffordRotation g).mulVec v ∈ unitSphere ∧
      sphereGate t ((bsCliffordRotation g).mulVec v) =
        cliffordMatrix g * sphereGate t v * star (cliffordMatrix g)) ∧
    Function.Injective (fun g : Fin 24 => fun v : {v : BsSphereVector // v ∈ unitSphere} =>
      (bsCliffordRotation g).mulVec v.val) ∧
    Set.range bsCliffordRotation = octahedronRotations ∧ Nat.card octahedronRotations = 24 ∧
    (⋃ g : Fin 24, tile g) = unitSphere ∧
    (∀ g h : Fin 24, g ≠ h → Disjoint (tileInterior g) (tileInterior h)) ∧
    Nat.card (Set.range tile) = 24 ∧ Nat.card tileVertices = 14 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P82

end
