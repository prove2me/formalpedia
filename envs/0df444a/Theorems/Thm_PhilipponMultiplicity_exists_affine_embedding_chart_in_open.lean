-- Prove2me | Theorems.Thm_PhilipponMultiplicity_exists_affine_embedding_chart_in_open
-- name    : PhilipponMultiplicity.exists_affine_embedding_chart_in_open
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T19:06:51.793988+00:00
-- url     : https://prove2.me/theorems/894b745f-508c-4656-8133-c35f91860a1f
-- title:
--   Affine embedding charts inside prescribed open neighborhoods
-- statement:
--   Let $K$ be an algebraically closed field, let
--   $$M=\prod_{b=1}^{r}\mathbf P^{d_b}_K,$$
--   and let $e:X\hookrightarrow M(K)$ have locally closed image. Give $X$ the induced Zariski topology. For every point $x\in X$ and open neighborhood $W$ of $x$, there exist an open subset $S$, a nonnegative integer $n$, a radical ideal $J\subseteq K[u_1,\ldots,u_n]$, and a homeomorphism
--   $$x\in S\subseteq W,\qquad a:S\xrightarrow{\sim}V(J),$$
--   with the following two coordinate properties.
--
--   First, there are polynomials $L_{b,j}\in K[u_1,\ldots,u_n]$ such that, for every $z\in S$, each block $(L_{b,j}(a(z)))_j$ is nonzero and represents the given projective point:
--   $$e(z)_b=[L_{b,0}(a(z)):\cdots:L_{b,d_b}(a(z))].$$
--
--   Second, for each affine coordinate $i$, there are multihomogeneous polynomials $P_i,Q_i$ in the coordinates of $M$, of the same multidegree, such that throughout $S$,
--   $$Q_i(e(z))\ne0,\qquad a(z)_i=\frac{P_i(e(z))}{Q_i(e(z))}.$$
--   Evaluation uses representatives of the projective points; equality of multidegrees makes the quotient independent of their scaling. The polynomials for a coordinate are fixed on all of $S$.
--
--   The affine zero set has its ordinary Zariski topology, equivalently the topology induced by the evaluation-ideal map into the prime spectrum of its polynomial ring. No irreducibility, positive-dimensionality, or characteristic-zero assumption is imposed.
--
--   **Formalization Note.** The proof constructs standard multiprojective chart homeomorphisms in the concrete Zariski topologies and converts affine polynomial fractions to balanced multihomogeneous fractions with nonzero denominators. The affine neighborhood construction is now proved as well, completing the chart theorem with both coordinate directions and refinement inside the prescribed open neighborhood. Every theorem dependency of the accepted reduction is now Proved, and this theorem has zero Open leaves. The final affine construction is [proved here](https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322). The original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Lemma 27.13.3, tag 01NG, https://stacks.math.columbia.edu/tag/01NG ; Section 26.5, tag 01HR, https://stacks.math.columbia.edu/tag/01HR , standard principal-open basis; Lemma 26.5.4(3), tag 01HV, https://stacks.math.columbia.edu/tag/01HV ; Lemma 26.10.1(3), tag 01IN, https://stacks.math.columbia.edu/tag/01IN . Auxiliary concrete-coordinate consequence: standard multiprojective charts, principal-open refinements of locally closed sets, and a reduced affine presentation with polynomial projective lifts and balanced homogeneous coordinate fractions. This is not a verbatim statement of a scheme lemma; the point-set topology and coordinate comparison remain obligations.

import Definitions.Def_PhilipponMultiplicity_Geometry
import Mathlib
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u

theorem exists_affine_embedding_chart_in_open
    (K : Type u) [Field K] [IsAlgClosed K]
    (M : MultiProjectiveSpace K) (X : Type u) (e : X → M.Point)
    (he : Function.Injective e)
    (hX : @IsLocallyClosed _ M.zariskiTopology (Set.range e))
    (x : X) (W : Set X)
    (hW : @IsOpen X (TopologicalSpace.induced e M.zariskiTopology) W)
    (hxW : x ∈ W) :
    letI : TopologicalSpace X := TopologicalSpace.induced e M.zariskiTopology
    ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
      ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
      ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
          (TopologicalSpace.induced
            (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
            inferInstance),
        (∃ L : M.Variable → MvPolynomial (Fin n) K,
          ∀ z : S, ∀ b, ∃ h :
            (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) ≠ 0,
            Projectivization.mk K
              (fun i => MvPolynomial.aeval (a z).val (L ⟨b, i⟩)) h = e z.val b) ∧
        (∀ i : Fin n, ∃ (D : M.FactorIndex → ℕ) (P Q : M.CoordinateRing),
          M.IsHomogeneous P D ∧ M.IsHomogeneous Q D ∧
          ∀ z : S, M.eval Q (e z.val) ≠ 0 ∧
            (a z).val i = M.eval P (e z.val) / M.eval Q (e z.val)) := by sorry

end PhilipponMultiplicity
