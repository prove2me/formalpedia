-- Prove2me | Theorems.Thm_QCSepTotal_lemma_2_2
-- name    : QCSepTotal.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:30.477406+00:00
-- url     : https://prove2.me/theorems/8d25fd28-e93e-45fd-bd54-84372eb9222b
-- title:
--   Lemma 2.2 — prediction from mutual information: $I(B:T\mid X)>\delta$ gives error $<1/2-\delta/2$
-- statement:
--   Let $B$ be a binary random variable and $X, T$ random variables on a finite probability space, and let $\delta>0$. If
--   $$I(B:T\mid X)>\delta ,$$
--   with conditional mutual information in bits, $I(A:B\mid C)=H(A\mid C)-H(A\mid B,C)$, then $B$ can be predicted from $(X,T)$ with error less than $1/2-\delta/2$: there is a function $\varphi$ with $\Pr[\varphi(X,T)\neq B]<1/2-\delta/2$.
--
--   It rules out "informative" protocols $\Pi_i$ in the proof of Theorem 4.1 (the case where (8) fails).
--
--   **Formalization Note** Conditional mutual information is the published `MultiphaseDisj.condMI` applied to the point masses of the distribution.
--
--   Differences from the source:
--   - encoding: random variables B, X, T and I(B : T | X) → functions on a finite sample space with a PMF, and MultiphaseDisj.condMI of its point masses; reason: same definition I(A:B|C) = H(A|C) − H(A|B,C) in bits
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), Lemma 2.2, p.3

import Mathlib
import Definitions.Def_MultiphaseDisj_FiniteInfo
import Definitions.Def_QCSepTotal_tv

namespace QCSepTotal

/-- **Lemma 2.2** (Prediction and mutual information; F. Le Gall, *Improved Separations between Quantum and Classical Communication Complexity of Total Functions*, arXiv:2609.16726 (held version, sha256 970e1476…), p.3). Let `B` be a
binary random variable and `X`, `T` random variables. If `I(B : T | X) > δ` for some `δ > 0`,
then `B` can be predicted from `(X, T)` with error less than `1/2 − δ/2`.

**Formalization Note.** The probability space is finite, `(Ω, P)` with `P` a `PMF`; the
conditional mutual information is the published `MultiphaseDisj.condMI` of the point masses,
`I(A : B | C) = H(A | C) − H(A | B, C)` in bits (p.3). -/
theorem lemma_2_2 {Ω α β : Type} [Fintype Ω] (P : PMF Ω) (B : Ω → Bool) (Xv : Ω → α)
    (T : Ω → β) (δ : ℝ) (hδ : 0 < δ)
    (h : δ < MultiphaseDisj.condMI (fun ω => (P ω).toReal) B T Xv) :
    ∃ φ : α × β → Bool, prob P {ω | φ (Xv ω, T ω) ≠ B ω} < 1 / 2 - δ / 2 := by sorry

end QCSepTotal
