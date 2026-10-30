-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P22_ppt_exponential_converse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P22.ppt_exponential_converse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T15:13:01.282509+00:00
-- url     : https://prove2.me/theorems/d4de73ab-1e79-477b-b012-7b9a1ea2db01
-- title:
--   Exponential bound on PPT-assisted transmission fidelity
-- statement:
--   Fix a finite-dimensional quantum channel $\mathcal N$, and write $r=R_{\max}(\mathcal N)$ for its max-Rains information in bits. For any $n$-use PPT-preserving-assisted protocol with positive integers $n,M$, define its rate $Q=(\log_2 M)/n$ and its actual squared transmission fidelity $f=\operatorname{Tr}(\Phi_M\omega)$, where $\omega$ is its computed output and $\Phi_M$ is the normalized maximally entangled projector. Then
--
--   $$f\le2^{-n(Q-r)}.$$
--
--   Consequently, an $(n,M,\varepsilon)$ protocol with $0<\varepsilon<1$ satisfies $1-\varepsilon\le2^{-n(Q-r)}$. Moreover, for each fixed margin $\Delta>0$, every such protocol with $Q\ge r+\Delta$ satisfies
--
--   $$f\le2^{-n\Delta}.$$
--
--   This gives a uniform exponential decay bound above any fixed positive rate margin. The fidelity guarantee $1-\varepsilon$ is kept distinct from the actual overlap $f$.
-- source:
--   Amortization does not enhance the max-Rains information of a quantum channel, arXiv:1709.04907v2, PDF p. 12, Remark 4 / eq. (66)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P22

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P22

open QAlgorithms QAlgorithms.Entanglement Filter Topology

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P35 (tr elog maxRelative)

open QAlgorithms.Papers.Independent.Support50.P21 (Le eMax)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pptPrime target)

open QAlgorithms.Papers.Independent.Dependency50.P09 (tensorAction)

open QAlgorithms.Papers.Independent.Information100.P04 (IsPPTChannel)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

section Statements

variable {A B C D L R : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype L] [Fintype R]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq L] [DecidableEq R]

variable [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty D] [Nonempty L] [Nonempty R]

/-- Remark 4, PDF p.12, (66): the guarantee and the actual squared fidelity
are distinguished. The last clause fixes a positive rate margin before n,M
and the protocol, giving a uniform exponential decay bound.
channelMaxRains.toReal is used only on finite-dimensional CPTP channels,
where the information quantity is finite; it is not an infinity fallback. -/
theorem ppt_exponential_converse (N : Superop A B) (hN : IsChannel N) :
    (∀ (n M : ℕ) (epsilon : ℝ), 0 < epsilon → epsilon < 1 →
      IsPPTProtocol N n M epsilon →
      1 - epsilon ≤ (2 : ℝ) ^
        (-(n : ℝ) * (communicationRate n M - (channelMaxRains N).toReal))) ∧
    (∀ (n M : ℕ) (omega : Mat (Fin M × Fin M)), IsProtocolOutput N n M omega →
      effectProb (target M) omega ≤ (2 : ℝ) ^
        (-(n : ℝ) * (communicationRate n M - (channelMaxRains N).toReal))) ∧
    (∀ delta : ℝ, 0 < delta → ∀ (n M : ℕ) (omega : Mat (Fin M × Fin M)),
      IsProtocolOutput N n M omega →
      (channelMaxRains N).toReal + delta ≤ communicationRate n M →
      effectProb (target M) omega ≤ (2 : ℝ) ^ (-(n : ℝ) * delta)) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Bridge50.P22

end
