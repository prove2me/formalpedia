-- Prove2me | Theorems.Thm_PauliMixedness_Randomized_pauli_influence_detectable
-- name    : PauliMixedness.Randomized.pauli_influence_detectable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:52:29.038782+00:00
-- url     : https://prove2.me/theorems/8a8e90e2-85f0-4d0d-b0a0-3b737d431558
-- title:
--   Lemma 2.2 — detectability of Pauli group influence
-- statement:
--   For every $N\ge1$ and every complex $N$-qubit density matrix $\rho$, let $L=\sum_{Q\ne I}\alpha_Q^2$ and $L_P=\sum_{S\ne\varnothing}3^{|S|}\alpha_P(S)^2$ for the coefficients computed from $\rho$. With $P$ uniform over all $3^N$ product Pauli settings,
--
--   $$\exists i\in\{1,\ldots,N\}:\quad\Pr[L_P\ge3^{i-2}L]\ge\frac{3^{-i}}N.$$
--
--   The statement includes $L=0$ and imposes no trace-distance or energy lower bound. It gives a detectable scale among the full family of Pauli settings.
--
--   Differences from the source:
--   - encoding: a mixed state with its Pauli decomposition and uniform setting probability → an arbitrary PSD trace-one complex matrix, computed trace coefficients and event cardinality divided by 3^N; reason: the decomposition follows from the Pauli basis and is not an added premise; finite counts give the exact uniform law
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #231 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/231.pdf, Lemma 2.2 p.6; proof p.24

import Definitions.Def_PauliMixedness_Randomized_QuantumModel

namespace PauliMixedness.Randomized

/-- Lemma 2.2 p.6; all nonidentity words and all 3^N settings. -/
theorem pauli_influence_detectable (N : ℕ) (hN : 1 ≤ N)
    (ρ : Operator N) (hρ : QAlgorithms.IsDensityMatrix ρ) :
    ∃ i : ℕ, 1 ≤ i ∧ i ≤ N ∧
      (3 : ℝ)^(-(i : ℤ)) / (N : ℝ) ≤
        ((Finset.univ.filter (fun P : Setting N =>
          (3 : ℝ)^((i : ℤ) - 2) * totalPauliEnergy ρ ≤ pauliInfluence ρ P)).card : ℝ) /
          (3 : ℝ)^N := by sorry

end PauliMixedness.Randomized
