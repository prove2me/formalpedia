-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_testBound_lt_rank_notPurifiable
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.testBound_lt_rank_notPurifiable
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:58:50.776972+00:00
-- url     : https://prove2.me/theorems/33170788-8665-4cbf-920b-aae79352f60f
-- title:
--   Necessary purification test in the balanced domain
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   Let $W$ be a valid bipartite process with trivial global past and future, let $r=\operatorname{rank}W$, and suppose $d_{A_I}d_{B_I}=d_{A_O}d_{B_O}$. Choose its positive spectral support, the canonical vector $w_0=\sum_{i=0}^{r-1}\sqrt{\lambda_i}\,|\lambda_i\rangle|i\rangle$, an orthonormal basis of $\ker O_W$, and a full orthonormal eigenbasis of the compression in Eq.(30). Here $O_W=(\langle w_0^*|\otimes I)\Pi_{L_V^\perp}(|w_0^*\rangle\otimes I)$, and $\Pi_{L_V^\perp}$ represents $I-L_V$ on input-first vectorized matrices. For every nonzero eigenmode, reshape it by $|M_k^T\rangle\!\rangle=|m_k\rangle$ and form $C_k=M_k+M_k^\dagger$ and $C_{k+d_m}=i(M_k-M_k^\dagger)$. Suppose this family is nonempty. With $n_+(C),n_-(C),n_0(C)$ counting eigenvalues with multiplicity, set $d_{\max}=\min_k[\min(n_+(C_k),n_-(C_k))+n_0(C_k)]$. Then
--
--   $$d_{\max}<r\quad\Longrightarrow\quad W\text{ is not purifiable}.$$
--
--   This is a necessary test only; its failure to obstruct purification gives no converse. The chosen bases are part of the data, rather than a basis-independence assertion.
--
--   Moreover, for every complex linear subspace $S$ of the kernel coordinate space, if $(I-L_V)(|\ell(v)\rangle\langle\ell(w)|)=0$ for every $v,w\in S$, then $\dim_{\mathbb C}S\le d_{\max}$. Here $\ell$ sends coordinates to their linear combination in the chosen orthonormal basis of $V_W$; it preserves complex dimension.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 7, §5, Eqs.(26)–(34)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF pp.6–7, §5, Eqs.(33)–(34): every bilinearly admissible subspace of VW
has dimension at most the computed bound, and the strict rank obstruction excludes
purification. Subspaces are expressed in the orthonormal kernel coordinates.
PRINTED: unrestricted laboratory dimensions. CHANGED: require total laboratory
input/output balance. WHY: the rank-sized reversible reconstruction in Theorem 4
is square only in this domain; the unrestricted reconstruction is deferred. -/
theorem testBound_lt_rank_notPurifiable {d : Fin 4 → ℕ+}
    (W : ProcessMatrix (laboratorySignature d 1 1)) (hW : IsValidProcess W)
    (e : SupportSpectrum W) (b : KernelBasisData e) (s : CompressionSpectrum b)
    (balanced : (d 0 : ℕ) * (d 2 : ℕ) = (d 1 : ℕ) * (d 3 : ℕ))
    (nonempty : ∃ k, s.values k ≠ 0) :
    (∀ S : Submodule ℂ (Fin b.dimension → ℂ),
      (∀ v ∈ S, ∀ w ∈ S,
        invalidSubspaceProjector
          (vectorOuter (liftKernelVector b v) (liftKernelVector b w)) = 0) →
      (Module.finrank ℂ S : WithTop ℕ) ≤ testBound s) ∧
    (testBound s < (Matrix.rank W : WithTop ℕ) → ¬ IsPurifiable W) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
