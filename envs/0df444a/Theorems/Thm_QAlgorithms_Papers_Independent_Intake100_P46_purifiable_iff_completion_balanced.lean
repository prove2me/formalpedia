-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P46_purifiable_iff_completion_balanced
-- name    : QAlgorithms.Papers.Independent.Intake100.P46.purifiable_iff_completion_balanced
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:04:41.312648+00:00
-- url     : https://prove2.me/theorems/4b978993-5a78-41e6-8994-69f64c9e4f4c
-- title:
--   Balanced purification characterization and reconstruction
-- statement:
--   All systems have positive finite dimensions and fixed computational bases. Choi operators are unnormalized and input first. A valid process maps every pair of local CPTP maps, with arbitrary ancillary input and output wires, to a CPTP map. Purity tests every compatible pair of local unitaries with those same ancillary extensions.
--
--   Let $W$ be valid with trivial global past and future, positive rank $r$, and positive spectral decomposition $W=\sum_{i=0}^{r-1}\lambda_i|\lambda_i\rangle\langle\lambda_i|$, with an orthonormal eigenfamily and multiplicities retained. Assume the proof-required correction $d_{A_I}d_{B_I}=d_{A_O}d_{B_O}$. Let $w_0=\sum_i\sqrt{\lambda_i}\,|\lambda_i\rangle|i\rangle$ on $A_I A_O B_I B_O F'$, where $\dim F'=r$. Then
--
--   $$W\text{ is purifiable}\quad\Longleftrightarrow\quad\exists(w_i)_{i=0}^{r-1}:\quad w_0\text{ has the prescribed value},\quad\forall i,j,\quad (I-L_V)(|w_i\rangle\langle w_j|)=0,\quad\langle w_i|w_j\rangle=d_{A_O}d_{B_O}\delta_{ij}.$$
--
--   Here $L_V$ is Eq.(64), specialized to a trivial global past and future dimension $r$. For every such family, define $U_s:P' A_O B_O\to A_I B_I F'$ by $\langle i|_{P'}|U_s\rangle\!\rangle=w_i$, where $\dim P'=\dim F'=r$. This constructed matrix is unitary; its Choi projector $S$ is a valid pure process and inserting $|0\rangle$ in $P'$ and tracing $F'$ recovers $W$.
--
--   Purifiability on the left allows arbitrary independent positive dimensions for the new past and future. The theorem therefore includes the rank-sized reconstruction, not only a positive-matrix purification.
-- source:
--   A purification postulate for quantum mechanics with indefinite causal order, arXiv:1611.08535v4, PDF p. 6, Theorem 4, corrected balanced domain

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P46

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.decEq Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Intake100.P46

/-- PDF pp.5–6, Theorem 4, corrected balanced domain. PRINTED: no condition relating
laboratory input and output dimensions. CHANGED: require dAI*dBI=dAO*dBO, as the
proof's dPprime=dFprime=rank(W) construction is square only then. The unrestricted
printed node is deferred. This states both directions and the actual reconstruction. -/
theorem purifiable_iff_completion_balanced {d : Fin 4 → ℕ+}
    (W : ProcessMatrix (laboratorySignature d 1 1)) (hW : IsValidProcess W)
    (e : SupportSpectrum W)
    (balanced : (d 0 : ℕ) * (d 2 : ℕ) = (d 1 : ℕ) * (d 3 : ℕ)) :
    (IsPurifiable W ↔ ∃ w, IsCompletion e w) ∧
    (∀ w, IsCompletion e w →
      IsReversibleMatrix (reconstructedUnitary e w) ∧
      IsValidProcess (processProjector (d := laboratorySignature d e.rank e.rank)
        (reconstructedUnitary e w)) ∧
      IsPureProcess (processProjector (d := laboratorySignature d e.rank e.rank)
        (reconstructedUnitary e w)) ∧
      recoverProcess (processProjector (d := laboratorySignature d e.rank e.rank)
        (reconstructedUnitary e w)) = W) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P46

end
