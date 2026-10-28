-- Prove2me | Theorems.Thm_QPurityAmp_Choi_prop_S2_1
-- name    : QPurityAmp.Choi.prop_S2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:31:27.207213+00:00
-- url     : https://prove2.me/theorems/8c732a8d-e467-47f0-a8b7-7d45d62c7c18
-- title:
--   Proposition S2.1, p. 18 — operators commuting with Ū ⊗ U^{⊗n} (U ∈ SU(d)) and with input permutations are scalar on each block [µ_i] of every ς-sector
-- statement:
--   Let $M$ be an operator on $\mathrm{out}\otimes\mathrm{in}=\mathbb C^d\otimes(\mathbb C^d)^{\otimes n}$ such that
--
--   1. $M$ commutes with $\bar U\otimes U^{\otimes n}$ for every $U\in SU(d)$, and
--   2. $M$ commutes with $\mathbb I_{\mathrm{out}}\otimes P_\pi$ for every permutation $\pi$ of the $n$ input registers.
--
--   Then for every Young diagram $\varsigma$ with $n$ boxes and at most $d$ rows there are complex numbers $m_i$, one for each feasible row $i$ of $\varsigma$, such that
--   $$M\,(\mathbb I_{\mathrm{out}}\otimes\Pi_\varsigma)=\sum_{\text{feasible } i} m_i\,P_{\mu_i}\,(\mathbb I_{\mathrm{out}}\otimes\Pi_\varsigma).$$
--   Here $\Pi_\varsigma$ is the weak Schur sampling projector and $P_{\mu_i}$ the projector onto the $[\mu_i]$-isotypic component of $\bar U\otimes U^{\otimes n}$, $[\mu_i]=\varsigma-e_i$.
--
--   This is the block decomposition $U^{[\varsigma]}_{CG}M^{[\varsigma]}U^{[\varsigma]\dagger}_{CG}=\bigoplus_{\text{feasible } i}m_i\mathbb I^{[\mu_i]}$ of Eq. (S17), which reduces the SDP for the optimal Choi matrix to a linear program in the coefficients $t_i$.
--
--   **Formalization Note** The paper states the proposition for an operator $M^{[\varsigma]}$ on $\mathbb V_{\mathrm{out}}\otimes W^{[\varsigma]}$, a single irrep block without its Specht multiplicity space. Here it is stated on the full space; the permutation invariance (hypothesis 2) is what removes the multiplicity $g^{[\varsigma]}$, as the paper does on p. 3 ("we can, without loss of generality, average over them"). Without it the statement is false when $g^{[\varsigma]}>1$. Row $i$ of the paper is Lean row $i-1$, and $[\mu_i]$ is encoded by the shifted diagram $\nu_i=\mu_i+(1^d)$.
-- source:
--   Li, Fu, Isogawa, Silva and Chuang, Optimal Quantum Purity Amplification, arXiv:2409.18167v4, p. 18, Proposition S2.1, Eq. (S17); p. 3, Eq. (3)

import Mathlib
import Definitions.Def_QPurityAmp_Choi_OptimalChoi
noncomputable section

namespace QPurityAmp.Choi

open scoped Matrix Kronecker

open QAlgorithms.Schur

/-- Proposition S2.1, p. 18 (Invariant Operator), restated on the full space out ⊗ W^{⊗n}.
An operator M that commutes with Ū ⊗ U^{⊗n} for every U ∈ SU(d), and with the permutations of
the n input registers, acts on the ς-sector out ⊗ Π_ς as a scalar m_i on each block
[µ_i], i feasible:
M (I ⊗ Π_ς) = Σ_{feasible i} m_i P_{µ_i} (I ⊗ Π_ς). -/
theorem prop_S2_1 {d n : ℕ}
    (M : Matrix (Fin d × (Fin n → Fin d)) (Fin d × (Fin n → Fin d)) ℂ)
    (hU : ∀ U ∈ Matrix.specialUnitaryGroup (Fin d) ℂ, M * mixedRep n U = mixedRep n U * M)
    (hperm : ∀ pi : Equiv.Perm (Fin n),
      M * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ tensorPermutation d n pi) =
        ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ tensorPermutation d n pi) * M)
    (vs : Partition d n) :
    ∃ m : {i : Fin d // IsFeasibleRow vs i} → ℂ,
      M * ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ isotypicProjector vs) =
        ∑ i, m i • blockProj vs i := by sorry

end QPurityAmp.Choi
