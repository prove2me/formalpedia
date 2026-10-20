-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P37_lemmaC10
-- name    : QAlgorithms.Papers.Independent.Dependency50.P37.lemmaC10
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:27:01.379996+00:00
-- url     : https://prove2.me/theorems/7386edd1-f605-4688-ae8f-b268138590f9
-- title:
--   Stabilized multiplicative domain and its finite descent
-- statement:
--   Let $\Phi:M_d(\mathbb C)\to M_d(\mathbb C)$ be a quantum channel, where $d\ge1$. Thus $\Phi$ is complex linear, completely positive, and trace preserving. Write $C_0,Q_0,C_{0E}$ for its one-shot, exactly zero-error classical, quantum, and entanglement-assisted classical capacities, measured with base-two logarithms and optimized over all allowed encodings. Powers of $\Phi$ mean sequential composition, with $\Phi^0$ the identity.
--
--   Assume $\Phi$ is unital. Let $\mathcal M_\Psi$ be the set of operators $A$ satisfying $\Psi(AX)=\Psi(A)\Psi(X)$ and $\Psi(XA)=\Psi(X)\Psi(A)$ for every $X$, and let $\mathcal M_\infty=\bigcap_{k\ge1}\mathcal M_{\Phi^k}$. Write $S_{\Phi^k}$ for the Kraus operator system and $S'$ for its ordinary commutant. Then
--
--   $$\mathcal M_\infty=\operatorname{alg}\{A:\Phi(A)=zA,\ |z|=1\},\qquad
--   \mathcal M_{\Phi^k}=S_{\Phi^k}'\quad(k\ge1).$$
--
--   If $\Phi$ is primitive, meaning mixing with a faithful invariant density, the stable domain is $\mathbb CI$, is attained after finitely many iterations, and the domains decrease strictly at every step whose current domain is not yet $\mathbb CI$.
--
--   This describes the algebraic stabilization of unital primitive dynamics. Part 1 is credited to [42]; part 2 uses the cited fixed-point identities.
--
--   **Formalization Note** The finite strict-descent qualification is the explicit final sentence of the proof, correcting the impossible infinite strict chain in the display.
-- source:
--   Zero-error communication under discrete-time Markovian dynamics, arXiv:2402.18703v3, PDF p. 26, Lemma C.10

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P37

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Dependency50.P37

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart operatorRange)

open QAlgorithms.Papers.Independent.Information100.P26 (commutant scalars)

open QAlgorithms.Papers.Independent.Information100.P62
  (classicalCapacity assistedCapacity quantumCapacity graph)

open QAlgorithms.Papers.Independent.Information100.P67 (complementaryChannel)

/-- Lemma C.10, PDF p.26. Part 1 is credited to [42]; part 2 uses the cited
fixed-point identities. SOURCE INTERPRETATION: part 3 is strict only while the
current domain is nonscalar, as explicitly stated in the final proof paragraph;
the printed infinite strict chain is impossible in finite dimension. -/
theorem lemmaC10 {d : ℕ} (hd : 0 < d) (Phi : Dynamics d) (hPhi : IsChannel Phi)
    (hunital : Phi 1 = 1) :
    stableMultiplicativeDomain Phi =
      (Algebra.adjoin ℂ {A : Operator d | ∃ z : ℂ, ‖z‖ = 1 ∧ Phi A = z • A} :
        Set (Operator d)) ∧
    (∀ k : ℕ, 0 < k → multiplicativeDomain (Nat.iterate Phi k) =
      commutant (graph (Nat.iterate Phi k) : Set (Operator d))) ∧
    (MixingWithFaithfulState Phi → stableMultiplicativeDomain Phi = (scalars d : Set (Operator d)) ∧
      (∃ N : ℕ, 0 < N ∧ ∀ n : ℕ, N ≤ n →
        multiplicativeDomain (Nat.iterate Phi n) = (scalars d : Set (Operator d))) ∧
      ∀ n : ℕ, 0 < n →
        multiplicativeDomain (Nat.iterate Phi (n + 1)) ⊆ multiplicativeDomain (Nat.iterate Phi n) ∧
        (multiplicativeDomain (Nat.iterate Phi n) ≠ (scalars d : Set (Operator d)) →
          multiplicativeDomain (Nat.iterate Phi (n + 1)) ⊂ multiplicativeDomain (Nat.iterate Phi n))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P37

end
