-- Prove2me | Theorems.Thm_PhilipponMultiplicity_affine_locally_closed_has_polynomial_fraction_charts
-- name    : PhilipponMultiplicity.affine_locally_closed_has_polynomial_fraction_charts
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-02T20:30:58.214601+00:00
-- url     : https://prove2.me/theorems/991f1acf-9ff2-4b25-ac1b-ae896736b322
-- title:
--   Polynomial and rational coordinates on locally closed affine neighborhoods
-- statement:
--   Let $K$ be an algebraically closed field and $\sigma$ a finite set of coordinate indices. Let $I\subseteq K[t_s:s\in\sigma]$ be any ideal, and give $V(I)\subseteq K^\sigma$ its Zariski topology. Let $X$ be a topological space and $d:X\hookrightarrow V(I)$ a topological embedding with locally closed image. For every $x\in X$ and open neighborhood $W$ of $x$, there exist an open subset $S$, a nonnegative integer $n$, a radical ideal $J\subseteq K[u_1,\ldots,u_n]$, and a homeomorphism
--   $$x\in S\subseteq W,\qquad a:S\xrightarrow{\sim}V(J),$$
--   with both of the following coordinate properties.
--
--   For each original coordinate $s\in\sigma$ there is a polynomial $L_s\in K[u_1,\ldots,u_n]$, fixed throughout $S$, such that
--   $$d(z)_s=L_s(a(z))\qquad(z\in S).$$
--   For each new coordinate $i$ there are polynomials $P_i,Q_i\in K[t_s:s\in\sigma]$, fixed throughout $S$, such that
--   $$Q_i(d(z))\ne0,\qquad a(z)_i=\frac{P_i(d(z))}{Q_i(d(z))}\qquad(z\in S).$$
--
--   Both affine zero sets have the topology induced by their evaluation-ideal maps into the respective polynomial prime spectra. No radicality assumption is placed on $I$, and neither irreducibility nor smoothness is assumed. The finite coordinate set may be empty, and $n$ may be zero.
--
--   **Formalization Note.** A complete Lean proof constructs the neighborhood by a principal-open refinement of a closed affine subset, followed by adjoining an inverse coordinate with equation $s q-1=0$. It proves the closed-subset presentation, radical graph ideal, inverse maps, both continuity directions in the evaluation-ideal topologies, and reindexing to finitely many numbered variables. The original coordinates are polynomial coordinate functions; every new coordinate is either $t_j/1$ or $1/q$ with nonzero denominator. The proof has no Open theorem dependencies, and the original formal statement and hypotheses are unchanged.
-- source:
--   Stacks Project, Section 26.5, tag 01HR, https://stacks.math.columbia.edu/tag/01HR , principal-open basis; Lemma 26.5.4(3), tag 01HV, https://stacks.math.columbia.edu/tag/01HV ; Lemma 26.10.1(3), tag 01IN, https://stacks.math.columbia.edu/tag/01IN . Auxiliary concrete-coordinate consequence: a principal-open refinement of a locally closed affine set has a polynomial graph presentation after adjoining the inverse of one polynomial. The homeomorphism and both coordinate comparisons in the stated evaluation-ideal topology remain proof obligations.

import Mathlib
set_option autoImplicit false

namespace PhilipponMultiplicity
universe u v w

theorem affine_locally_closed_has_polynomial_fraction_charts
    (K : Type u) [Field K] [IsAlgClosed K]
    (σ : Type v) [Finite σ] (I : Ideal (MvPolynomial σ K))
    (X : Type w) [TopologicalSpace X] :
    letI : TopologicalSpace (MvPolynomial.zeroLocus K I) :=
      TopologicalSpace.induced
        (fun z : MvPolynomial.zeroLocus K I => MvPolynomial.pointToPoint (k := K) z.val)
        inferInstance
    ∀ (d : X → MvPolynomial.zeroLocus K I), Topology.IsEmbedding d →
      IsLocallyClosed (Set.range d) →
      ∀ (x : X) (W : Set X), IsOpen W → x ∈ W →
        ∃ S : Set X, IsOpen S ∧ x ∈ S ∧ S ⊆ W ∧
          ∃ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) K)), J.IsRadical ∧
          ∃ a : @Homeomorph S (MvPolynomial.zeroLocus K J) inferInstance
              (TopologicalSpace.induced
                (fun z : MvPolynomial.zeroLocus K J => MvPolynomial.pointToPoint (k := K) z.val)
                inferInstance),
            (∃ L : σ → MvPolynomial (Fin n) K,
              ∀ z : S, ∀ t, (d z.val).val t = MvPolynomial.aeval (a z).val (L t)) ∧
            (∀ i : Fin n, ∃ P Q : MvPolynomial σ K,
              ∀ z : S, MvPolynomial.aeval (d z.val).val Q ≠ 0 ∧
                (a z).val i = MvPolynomial.aeval (d z.val).val P /
                  MvPolynomial.aeval (d z.val).val Q) := by sorry

end PhilipponMultiplicity
