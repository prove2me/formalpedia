-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P75_redistribution_achievability
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P75.redistribution_achievability
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:50:46.533434+00:00
-- url     : https://prove2.me/theorems/7dfd42d1-47da-47f1-bc5e-c1ec09dc18d3
-- title:
--   Asymptotic state redistribution at half the conditional mutual information
-- statement:
--   Let $\psi_{ABCR}$ be any pure density operator on finite-dimensional nonzero complex systems and put $\rho_{ABC}=\operatorname{tr}_R\psi$. A sender holding $AR$ transfers $A$ to a receiver holding $C$, with $B$ untouched. Each protocol has arbitrary independent shared density operator $\Phi_{T_AT_B}$, a CPTP encoder $ART_A\to QR$, and a CPTP decoder $CQT_B\to A'C$, with $A'\cong A$. Fidelity compares the full output, including $R$, with $\psi$.
--
--   There exist protocols for $m$ copies, positive numbers $\varepsilon_m<1/12$ tending to zero, and a convergent communication rate $r$ such that, writing $\widehat\psi_m$ for the full reconstructed state and $q_m=\log_2\dim Q_m$,
--
--   $$
--   F(\widehat\psi_m,\psi^{\otimes m})\ge1-144\varepsilon_m^2,
--   \qquad \lim_{m\to\infty}\frac{q_m}{m}=r\le\frac12 I(A:B|C)_\rho.
--   $$
--
--   Here $F$ is squared fidelity and $I(A:B|C)=H(AC)+H(BC)-H(ABC)-H(C)$ uses entropy in bits. This is an achievability statement with a chosen vanishing error schedule.
--
--   **Formalization Note** Lean indexes positive block lengths by $m=n+1$. The smooth-entropy upper bound in (34) is the derivation of the final asymptotic rate, rather than a separately asserted one-shot bound.
-- source:
--   The Fidelity of Recovery is Multiplicative, arXiv:1502.07973v2, PDF p. 6, Section IV, (34)–(36)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P75

namespace QAlgorithms.Papers.Independent.Intakenext100.P75

open scoped Matrix ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P53 (fidelity)

open QAlgorithms.Papers.Independent.Information100.P08 (IsPure)

open QAlgorithms.Papers.Independent.Dependency50.P18 (bipartiteTensor)

variable {A B C D Ap Bp Cp R I J K L : Type}

variable [Fintype A] [DecidableEq A] [Nonempty A]

variable [Fintype B] [DecidableEq B] [Nonempty B]

variable [Fintype C] [DecidableEq C] [Nonempty C]

variable [Fintype D] [DecidableEq D] [Nonempty D]

variable [Fintype Ap] [DecidableEq Ap] [Nonempty Ap]

variable [Fintype Bp] [DecidableEq Bp] [Nonempty Bp]

variable [Fintype Cp] [DecidableEq Cp] [Nonempty Cp]

variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- PDF p.6, (34)–(36): actual full-state redistribution protocols with
vanishing infidelity and a convergent communication rate at most I(A:B|C)/2.
The vanishing smoothing schedule is existential, not arbitrary. -/
theorem redistribution_achievability
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty R] (psi : Mat (B × (R × (A × C))))
    (hpure : IsPure psi) :
    ∃ protocols : (n : ℕ) → Redistribution (Fin (n + 1) → A) (Fin (n + 1) → C)
        (Fin (n + 1) → R),
    ∃ epsilon : ℕ → ℝ, ∃ rate : ℝ,
      (∀ n, 0 < epsilon n ∧ epsilon n < 1 / 12) ∧
      Filter.Tendsto epsilon Filter.atTop (nhds 0) ∧
      (∀ n, 1 - 144 * epsilon n ^ 2 ≤
        fidelity ((protocols n).output (fullCopies psi (n + 1)))
          (fullTarget (fullCopies psi (n + 1)))) ∧
      Filter.Tendsto (fun n => (protocols n).cost / (n + 1 : ℝ)) Filter.atTop (nhds rate) ∧
      rate ≤ conditionedLastCMIBits (discardReference psi) / 2 := by sorry

end QAlgorithms.Papers.Independent.Intakenext100.P75
