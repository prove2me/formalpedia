-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_Supplement_fixed_pauli_covariance
-- name    : PauliMixedness.Randomized.Supplement.fixed_pauli_covariance
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T16:58:05.820879+00:00
-- url     : https://prove2.me/theorems/056e0d30-d6ee-4af3-b201-0b750ecec3d8
-- title:
--   Lemma 4.1 (corrected: all subsets, including empty) — covariance identity
-- statement:
--   For every integer $N\ge0$ and every complex $N$-qubit density matrix $\rho$, write $\alpha_Q=\operatorname{Re}\operatorname{Tr}(Q\rho)$ and $\alpha_P(S)=\alpha_{P^S}$, where $P\in\{X,Y,Z\}^N$ and $P^S$ has identity outside $S$. With $w(Q)$ the number of nonidentity wires,
--
--   $$\sum_{P\in\{X,Y,Z\}^N}\sum_{S,S'\subseteq[N]}\frac{\alpha_P(S\triangle S')^2}{3^{N-|S|}3^{N-|S'|}}=\left(\frac{10}{3}\right)^N+\left(\frac{10}{3}\right)^N\sum_{Q\ne I}\frac{\alpha_Q^2}{5^{w(Q)}}.$$
--
--   Both inner sums include the empty subset and $\alpha_P(\varnothing)=1$. The right sum omits the all-identity word. This identity controls the covariance sum in the fixed-measurement tester; its upper bound also bounds the smaller nonempty-subset sum used in §4.1.
--
--   Differences from the source:
--   - correction: S and S′ are nonempty subsets → S and S′ range over all subsets, including the empty subset; reason: at N=1 and ρ=I/2 the printed left side is 3 but its right side is 10/3; including the identity pairs gives 10/3 and matches Appendix B
--   - encoding: one-based wires and nonidentity Pauli words on the right → Fin N wires and a sum over all Word N with the identity term set to zero; reason: zero-based indexing and filtering change no coefficient or instance
--   - correction: the global identity coefficient is inconsistently printed as 1/d on p.9 → the inherited published convention α_I = Re Tr(Iρ) = 1 on states; reason: for N=1 and ρ=I/2 the trace coefficient is 1, not 1/2; Appendix B uses this trace-one identity coefficient for its constant term
--   - generalization: an N-qubit system (N ≥ 1 implicit) → every N : ℕ, including N = 0; reason: at N = 0 both sides equal 1 (one empty setting, S = S′ = ∅, α(∅) = Tr ρ = 1; no non-identity word), so the Lean statement contains the source's instances N ≥ 1 unchanged
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Lemma 4.1 p.14; Appendix B p.27

import Definitions.Def_PauliMixedness_Randomized_Supplement_Measurements

open scoped BigOperators

namespace PauliMixedness.Randomized.Supplement

/-- Lemma 4.1 p.14 (corrected: all subsets, including empty), proof App. B p.27.
At N=1 and ρ=I/2, the printed nonempty-only left side is 3 while the right
side is 10/3. App. B's counting includes the missing identity pairs. -/
theorem fixed_pauli_covariance (N : ℕ)
    (ρ : Operator N) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    (∑ P : Setting N, ∑ S : Finset (Fin N), ∑ T : Finset (Fin N),
      basisCoeff ρ P (symmDiff S T) ^ 2 /
        ((3 : ℝ)^(N - S.card) * (3 : ℝ)^(N - T.card))) =
      (10 / 3 : ℝ)^N + (10 / 3 : ℝ)^N *
        ∑ Q : Word N, if Q = (fun _ => 0) then 0 else
          pauliCoeff ρ Q ^ 2 / (5 : ℝ)^wordWeight Q := by sorry

end PauliMixedness.Randomized.Supplement
