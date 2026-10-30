-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_processor_symmetrization
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.processor_symmetrization
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:11:37.95358+00:00
-- url     : https://prove2.me/theorems/9bf4d6fd-7129-4713-9c22-f4ff18643e32
-- title:
--   Proposition 14: symmetrizing a processor
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. For every $p>0$, $\varepsilon\ge0$, and $\varepsilon$-processor $P$ for $\mathcal T_{UV}$, there is an $\varepsilon$-processor $P^\prime$ on the same program space such that
--
--   $$P^\prime((U_g\otimes I_p)X(U_g\otimes I_p)^*)=V_gP^\prime(X)V_g^*\quad\text{for every }g,X.$$
--
--   Every original density program meeting the error guarantee still meets it for $P^\prime$. Neither representation is assumed irreducible. This permits covariance of the processor itself without increasing memory.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 7, Proposition 14: symmetrizing a processor

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P21

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Manifold ContDiff

open QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Support21.P09 (Irreducible EquivalentModels)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P08 (depolarizing)

open QAlgorithms.Papers.Independent.Information100.P60 (wernerHolevo)

namespace QAlgorithms.Papers.Independent.Extend50.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

section General

variable {G I O : Type*} [Group G] [TopologicalSpace G]

variable [Fintype I] [DecidableEq I] [inputNonempty : Nonempty I]

variable [Fintype O] [DecidableEq O] [outputNonempty : Nonempty O]

include inputNonempty outputNonempty

/-- PDF p.7, Proposition 14: symmetrization uses the same program register;
no irreducibility hypothesis occurs here. -/
theorem processor_symmetrization (hG : CompactLie G) (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O)
    (p : ℕ) (hp : 0 < p) (epsilon : ℝ) (he : 0 ≤ epsilon)
    (processor : Superop (I × Fin p) O)
    (hP : ProgramsChannelClass processor (covariantChannels U.mat V.mat) epsilon) :
    ∃ newProcessor : Superop (I × Fin p) O,
      ProgramsChannelClass newProcessor (covariantChannels U.mat V.mat) epsilon ∧
      OperatorCovariant (fun g => Matrix.kronecker (U.mat g) (1 : Matrix (Fin p) (Fin p) ℂ))
        V.mat newProcessor ∧
      ∀ T ∈ covariantChannels U.mat V.mat, ∀ program : Matrix (Fin p) (Fin p) ℂ,
        IsDensityMatrix program →
        diamond (fun A => programmedChannel processor program A - T A) / 2 ≤ epsilon →
        diamond (fun A => programmedChannel newProcessor program A - T A) / 2 ≤ epsilon := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
