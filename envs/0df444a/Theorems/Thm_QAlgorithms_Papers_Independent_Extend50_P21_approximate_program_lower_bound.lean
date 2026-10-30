-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P21_approximate_program_lower_bound
-- name    : QAlgorithms.Papers.Independent.Extend50.P21.approximate_program_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:24:41.993145+00:00
-- url     : https://prove2.me/theorems/e2da57a8-6212-4177-9d2e-d83369bffc73
-- title:
--   Theorem 31: approximate program dimension lower bound
-- statement:
--   All Hilbert spaces are nonzero and finite dimensional over $\mathbb C$. Channels are completely positive and trace preserving (CPTP), density operators are positive semidefinite with trace one, and pure programs are unit vectors. Let $G$ be a compact Lie group, $U$ a continuous unitary representation on the input $\mathcal H_1$, and $V$ one on the output $\mathcal H_2$, of dimensions $d_1,d_2>0$. Write $\mathcal T_{UV}$ for the CPTP maps satisfying $T(U_gAU_g^*)=V_gT(A)V_g^*$ for every operator $A$ and $g\in G$. In an actual unitary isotypic decomposition $\overline U\otimes V\simeq\bigoplus_{k=1}^K W_k\otimes I_{n_k}$, the $W_k$ are pairwise inequivalent occurring irreducibles with positive dimensions $b_k$, and $n_k>0$ are their multiplicities. Put $d_c=\sum_k n_k$ and $d_n=\sum_k n_k^2$. A processor is one fixed CPTP map $P:\mathcal B(\mathcal H_1\otimes\mathbb C^p)\to\mathcal B(\mathcal H_2)$, chosen before the target channel. An $\varepsilon$-processor means that every target $T$ has a density program $\pi_T$ with $\frac12\|P(\cdot\otimes\pi_T)-T\|_\diamond\le\varepsilon$, including entangled reference inputs. Assume $U$ is irreducible. For every $0\le\varepsilon<1$, every fixed $\varepsilon$-processor for the entire class, of positive program dimension $p$, satisfies
--
--   $$p\ge2^{-2h_2(\varepsilon)}d_c^{1-2\varepsilon},\qquad h_2(t)=-t\log_2t-(1-t)\log_2(1-t),$$
--
--   with $0\log_2 0=0$. Mixed programs are allowed. The complete inequality is printed on page 21; page 19 omits its left side. At zero error this gives $p\ge d_c$, the matching exact lower bound. The negative exponent when $\varepsilon>1/2$ is retained.
-- source:
--   Programmability of covariant quantum channels, arXiv:2012.00717v2, PDF p. 19, Theorem 31: approximate program dimension lower bound

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

/-- PDF pp.19--21, Theorem 31: completed inequality from p.21, binary entropy
in bits, mixed programs permitted, and the full printed interval [0,1). The
erroneous minus-entropy continuity line on p.20 is not used as a statement. -/
theorem approximate_program_lower_bound (hG : CompactLie G)
    (U : ContinuousUnitaryRep G I) (V : ContinuousUnitaryRep G O) (hU : Irreducible U.mat) (D : TensorIsotypicDecomposition U V)
    (epsilon : ℝ) (he0 : 0 ≤ epsilon) (he1 : epsilon < 1)
    (p : ℕ) (hp : 0 < p) (processor : Superop (I × Fin p) O)
    (hP : ProgramsChannelClass processor (covariantChannels U.mat V.mat) epsilon) :
    Real.rpow (2 : ℝ) (-2 * binEntropy2 epsilon) *
      Real.rpow (compressedDim D : ℝ) (1 - 2 * epsilon) ≤ (p : ℝ) := by sorry

end General

end QAlgorithms.Papers.Independent.Extend50.P21

end
