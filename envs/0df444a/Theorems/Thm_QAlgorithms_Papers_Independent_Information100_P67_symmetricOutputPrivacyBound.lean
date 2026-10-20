-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P67_symmetricOutputPrivacyBound
-- name    : QAlgorithms.Papers.Independent.Information100.P67.symmetricOutputPrivacyBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:55:09.656565+00:00
-- url     : https://prove2.me/theorems/fa6428d2-db9c-4805-9b11-4a368dbd26e6
-- title:
--   Proposition 4.3 (Symmetric-output privacy bound)
-- statement:
--   There are universal $C_{\rm app}\ge1$ and $a=1/(4C_{\rm app}^2)>0$ with the following property. Let $\theta$ be any normalized state on $KSC\bigotimes_{j=1}^n(B_{j,0}B_{j,1})$, where $|K|=M\ge1$, $|C|=L$, and both factors in each pair have the same positive dimension $d$. Assume invariance under every individual swap $B_{j,0}\leftrightarrow B_{j,1}$. Choose one unitary decoder on $CB_{0^n}G$, one initialized local pure auxiliary ket in $G$, and one size-$M$ privacy test on the decoded key and the sender/receiver shields. Let $p$ be this test's acceptance probability. For every $n\ge1$ and integer $t$ satisfying $4C_{\rm app}\sqrt n\le t\le n/2$,
--
--   $$p\le2e^{-at^2/n}+\left(\sum_{j=0}^t\binom nj\right)^{1/4}\sqrt{\min\{1,Ld^t/M\}}.$$
--
--   The key marginal may be nonuniform and $C$ may be correlated with all other systems. Alternative placements are relabelings of this one decoder and test, each with a separate local auxiliary, as in Section 4.1.
-- source:
--   An exponential strong converse for private communication over degradable quantum channels, arXiv:2609.32515v1, PDF p. 17, Proposition 4.3 (Symmetric-output privacy bound)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Information100.P67

variable {A B E R S T X C Y G1 G2 : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype R] [DecidableEq R]

variable [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

variable [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]

variable [Fintype Y] [DecidableEq Y] [Fintype G1] [DecidableEq G1]

variable [Fintype G2] [DecidableEq G2]

/-- Proposition 4.3, PDF pp.17–18,22–23. Universal constants precede all
systems. EVERY independent pair swap is assumed, and the fixed mathematical
decoder/test uses a retained local pure auxiliary. No key prior is assumed. -/
theorem symmetricOutputPrivacyBound :
    ∃ Capp : ℝ, 1 ≤ Capp ∧ ∃ a : ℝ, 0 < a ∧ a = 1 / (4 * Capp ^ 2) ∧
    ∀ (S C B G T : Type) [Fintype S] [DecidableEq S] [Nonempty S]
      [Fintype C] [DecidableEq C] [Nonempty C]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype G] [DecidableEq G] [Nonempty G]
      [Fintype T] [DecidableEq T] [Nonempty T],
    ∀ n M : ℕ, 0 < n → 0 < M → ∀ t : ℕ,
      4 * Capp * Real.sqrt n ≤ (t : ℝ) → (t : ℝ) ≤ (n : ℝ) / 2 →
    ∀ theta : Matrix (Fin M × (S × (C × ((Fin n → B) × (Fin n → B)))))
      (Fin M × (S × (C × ((Fin n → B) × (Fin n → B))))) ℂ,
      IsDensityMatrix theta →
      (∀ j : Fin n, ∀ x y,
        theta (swapReceiverCoordinate j x) (swapReceiverCoordinate j y) = theta x y) →
    ∀ (g : G) (D : Matrix (Fin M × T) (C × ((Fin n → B) × G)) ℂ),
      (Dᴴ * D = 1 ∧ D * Dᴴ = 1) →
    ∀ twist : Fin M → Matrix (S × T) (S × T) ℂ,
      (∀ m, twist m ∈ Matrix.unitaryGroup _ ℂ) →
      (decodedPrivacyTest twist D * symmetricReceiverMarginal theta g).trace.re ≤
        2 * Real.exp (-a * (t : ℝ) ^ 2 / n) +
          Real.rpow (binomialVolume n t) (1 / 4 : ℝ) *
            Real.sqrt (min 1 ((Fintype.card C : ℝ) * (Fintype.card B : ℝ) ^ t / M)) := by sorry

end QAlgorithms.Papers.Independent.Information100.P67

end
