-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P35_prettyStrongConverse
-- name    : QAlgorithms.Papers.Independent.Bridge50.P35.prettyStrongConverse
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:12:44.426467+00:00
-- url     : https://prove2.me/theorems/2747310e-30f2-4119-ac17-5a913249016f
-- title:
--   Finite-block pretty strong converse for degraded cqq wiretap channels
-- statement:
--   Let $X$ be a finite nonempty classical alphabet and let $B,E$ be finite positive-dimensional complex Hilbert spaces. Let $W:x\mapsto\rho_x^{BE}$ be a memoryless cqq channel, with each output a density operator. Suppose a CPTP map $\mathcal D:B\to E$ satisfies $\mathcal D(\rho_x^B)=\rho_x^E$ for every $x$. An unassisted length-$n$ code uses a stochastic encoder into $X^n$ and a POVM on $B^n$ to transmit a uniform message. Its transmission error is $P(\rho^{U\widehat U},\Delta^{U\widehat U})$; its secrecy error is the least $P(\rho^{UE^n},\Delta^U\otimes\sigma^{E^n})$ over normalized $\sigma$. Here $P(\rho,\sigma)=\sqrt{1-F(\rho,\sigma)^2}$ uses unsquared root fidelity. Write $M_W(n,\epsilon,\delta)$ for the largest admissible message count, and $P(W)$ for the operational capacity with both errors vanishing.
--
--   Fix $W$ and $s\in(0,1]$. There exist $C>0$ and an integer $n_0\ge2$, depending on $W$ and $s$, such that for every $n\ge n_0$ and every $\epsilon,\delta\ge0$ satisfying $1-\epsilon-2\delta=s$,
--   $$
--   \log_2 M_W(n,\epsilon,\delta)\le nP(W)+C\sqrt{n\log_2 n}.
--   $$
--   Thus the constants are uniform over codes and error pairs with the same slack, for the fixed channel. This is the finite-block pretty strong converse in the region $\epsilon+2\delta<1$.
--
--   **Formalization Note** The optimal logarithmic message count and operational capacity use extended-real suprema and infima. They are finite on this theorem's domain, so the displayed inequality has its ordinary real meaning. The capacity is defined operationally, by the infimum over positive tolerances of the liminf block rate.
-- source:
--   "Pretty strong" converse for the private capacity of degraded quantum wiretap channels, arXiv:1601.06611v2, PDF p. 2, Theorem 2, finite-block pretty strong converse (original seed)

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P35

noncomputable section

namespace QAlgorithms.Papers.Independent.Bridge50.P35

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Dependency50.P48 (cqPower)

open QAlgorithms.Papers.Independent.Information100.P56 (PrivateCode)

open QAlgorithms.Papers.Independent.Information100.P67
  (purifiedDistance idealClassicalKey)

attribute [local instance] Classical.propDecidable

variable {X B E : Type*}

variable [Fintype X] [DecidableEq X]

variable [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E]

/-- Theorem 2, PDF p.2, proof pp.2–4: the finite-block pretty strong converse.
For each fixed channel and fixed slack s, constants are chosen before the
blocklength and before every error pair having that slack. The source's
s-only dependence describes error dependence at fixed W, not a uniform
bound over all channel dimensions. The printed endpoint limit is omitted
here and documented separately as defective. -/
theorem prettyStrongConverse [Nonempty X] [Nonempty B] [Nonempty E]
    (W : CqqChannel X B E) (hW : W.IsDegraded)
    (s : ℝ) (hs : 0 < s) (hsone : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, 2 ≤ n0 ∧
      ∀ n : ℕ, n0 ≤ n → ∀ epsilon delta : ℝ,
        0 ≤ epsilon → 0 ≤ delta → 1 - epsilon - 2 * delta = s →
          logMessageNumber W n epsilon delta ≤
            (n : EReal) * cqqPrivateCapacity W +
              (C * Real.sqrt ((n : ℝ) * Real.logb 2 (n : ℝ)) : EReal) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P35

end
