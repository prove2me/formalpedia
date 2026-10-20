-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P06_completion_iff
-- name    : QAlgorithms.Papers.Independent.Dependency50.P06.completion_iff
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T13:20:29.815325+00:00
-- url     : https://prove2.me/theorems/81d7fb13-db44-4ef9-ac9e-a2792ecfe2cc
-- title:
--   Superchannel completion exactly characterizes complete CPTNI preservation
-- statement:
--   All quantum systems below have finite, nonzero dimension, with fixed orthonormal bases; one-dimensional systems are allowed. A channel system $A=(A_0,A_1)$ consists of an input and an output system, and likewise for $B$. A map is complex-linear on its full operator space. Density matrices are positive semidefinite with trace one. Let $\Theta:A\to B$ be CPTNI-preserving: it is completely CP-preserving (CPP), and sends each channel on $A$ to a CPTNI map on $B$. A superchannel is CPP and preserves channels under every identity-supermap extension. Then
--
--   $$\exists\Theta^{\prime}\;[\Theta^{\prime}\text{ is CPTNI-preserving and }\Theta+\Theta^{\prime}\text{ is a superchannel}]\quad\Longleftrightarrow\quad\Theta\text{ is completely CPTNI-preserving}.$$
--
--   The complementary branch is a linear supermap on all maps. Complete CPTNI preservation means that every bipartite channel is sent to a CPTNI map by $1_R\otimes\Theta$, for every finite ancillary input/output pair $R$. This characterizes the branches that can occur in measurements of channels.
-- source:
--   Necessary and Sufficient Conditions on Measurements of Quantum Channels, arXiv:1904.09161v5, PDF p. 15, Theorem D.1; Theorem 4.1 (p.4)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P06

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P06

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P22 (Op mixed)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section QuantumResults

variable {A0 A1 B0 B1 : Type}

variable [Fintype A0] [Fintype A1] [Fintype B0] [Fintype B1]

variable [hA0 : Nonempty A0] [hA1 : Nonempty A1] [hB0 : Nonempty B0] [hB1 : Nonempty B1]

/-- PDF pp.4,15, Theorems 4.1 and D.1: completion by another CPTNI-preserving
supermap is equivalent to complete CPTNI preservation. -/
theorem completion_iff (S : Supermap A0 A1 B0 B1) (hS : IsCPTNIPreserving S) :
    (∃ T : Supermap A0 A1 B0 B1, IsCPTNIPreserving T ∧ IsSuperchannel (S + T)) ↔
      IsCompletelyCPTNIPreserving S := by sorry

end QuantumResults

end QAlgorithms.Papers.Independent.Dependency50.P06

end
