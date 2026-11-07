-- Prove2me | Theorems.Thm_PolySphereLP_lemma_A_4_null_cone
-- name    : PolySphereLP.lemma_A_4_null_cone
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:59:28.506701+00:00
-- url     : https://prove2.me/theorems/a1cd9799-bd4e-401a-8820-aff363b63329
-- title:
--   Lemma A.4 — the trace-free projection is invisible on the null cone
-- statement:
--   Let $G$ be a homogeneous polynomial of degree $k$, possibly with complex coefficients, and let $G_k=\Pi_kG$ be its top harmonic component (Fischer decomposition).
--   1. If $z\in\mathbb C^n$ satisfies $z^\top z=0$, then $G_k(z)=G(z)$. (60)
--   2. Equivalently, if $T_G$ and $T_{G_k}$ are their symmetric coefficient tensors, every isotropic frame $V$ ($V^*V=I_m$, $V^\top V=0$) satisfies $R_VT_{G_k}=R_VT_G$. (61)
--
--   On the image of an isotropic frame all trace corrections vanish, which is how the top harmonic component of a power is computed in Proposition A.6.
--
--   **Formalization Note** $z^\top z=\sum_iz_i^2$ with no conjugation. The frame size $m$ is arbitrary.
--
--   Differences from the source:
--   - generalization: isotropic frame V with m = ⌊n/2⌋ columns (§A.6) → any n × m complex matrix with V*V = I_m and VᵀV = 0, for every m; reason: the proof uses only VᵀV = 0; the case m = ⌊n/2⌋ is included
--   - generalization: standing assumption n ≥ 3 (§2, p.9) → any n; reason: the lemma is algebraic and the Fischer decomposition exists for every n; the case n ≥ 3 is included
--   - encoding: Π_k G → fischerTopC n k G (the Fischer top component of (16) over ℂ); reason: the definition of Π_k on homogeneous polynomials in (16)
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Lemma A.4, p.28, eqs. (60)–(61)

import Mathlib
import Definitions.Def_PolySphereLP_fischerTopC
import Definitions.Def_PolySphereLP_coeffTensor
import Definitions.Def_PolySphereLP_restrictT
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Lemma A.4 (Trace-free projection is invisible on the null cone).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Lemma A.4, p.28,
eqs. (60)–(61).

Let `G` be a homogeneous polynomial of degree `k`, possibly with complex coefficients, and
`G_k = Π_k G` its top harmonic component. If `z ∈ ℂⁿ` satisfies `zᵀz = 0`, then `G_k(z) = G(z)` (60).
Equivalently, every isotropic frame `V` (`V*V = I_m`, `VᵀV = 0`) satisfies `R_V T_{G_k} = R_V T_G` (61).

**Formalization Note.** `Π_k G` is the Fischer top component `fischerTopC` of (16) over `ℂ`.
`zᵀz = ∑ zᵢ²` (no conjugation). Frames are `n × m` complex matrices for any `m` (the paper uses
`m = ⌊n/2⌋`). -/
theorem lemma_A_4_null_cone (n k : ℕ) (G : MvPolynomial (Fin n) ℂ) (hG : G.IsHomogeneous k) :
    (∀ z : Fin n → ℂ, ∑ i, z i ^ 2 = 0 → eval z (fischerTopC n k G) = eval z G) ∧
    (∀ (m : ℕ) (V : Matrix (Fin n) (Fin m) ℂ), V.conjTranspose * V = 1 → V.transpose * V = 0 →
      restrictT k V (coeffTensor k (fischerTopC n k G)) = restrictT k V (coeffTensor k G)) := by sorry

end PolySphereLP
