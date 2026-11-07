-- Prove2me | Theorems.Thm_SamplingAC0_lemma_9
-- name    : SamplingAC0.lemma_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:45:44.370466+00:00
-- url     : https://prove2.me/theorems/1823459e-95bc-429b-8ea0-91ba77288b92
-- title:
--   Lemma 9 — fixed-set lemma [GSV18] with the fixing probability
-- statement:
--   There is an absolute constant $c>0$ such that the following holds. Let $D$ be uniform on a set $A\subseteq\{0,1\}^n$ of size at least $2^{n-a}$, and let $U$ be uniform on $\{0,1\}^n$. Then for any $\eta>0$ and any $s$ there are $B\subseteq[n]$ and $v\in\{0,1\}^B$ with
--
--   $$\lvert B\rvert\le\frac{c\,a\,s}{\eta}$$
--
--   such that, writing $D'=(D\mid D_B=v)$ and $R=(U\mid U_B=v)$,
--
--   1. the fixing has probability $\mathbb P[D_B=v]\ge2^{-\lvert B\rvert}$, and
--   2. every decision tree $T$ of depth at most $s$ satisfies $\Delta(T(D'),T(R))\le\eta$.
--
--   The lemma (from [GSV18, Lemma 3.14]) says that a high-min-entropy distribution becomes indistinguishable from uniform by shallow decision trees after fixing a few coordinates. Clause 1 is stated in the paper as a further consequence of the proof in [GSV18]; the proof of Theorem 1 uses it.
--
--   **Formalization Note** Decision trees may have any finite output type. $v$ is given as a full assignment of which only the coordinates in $B$ are read. The mission poses this lemma; its proof is in [GSV18], not in this paper.
--
--   Differences from the source:
--   - generalization: every decision tree T of depth ≤ s (output type unspecified) → decision trees with any finite output type; reason: trees with Boolean or vector outputs are special cases
--   - generalization: Lemma 9 as printed → Lemma 9 together with P[D_B = v] ≥ 2^{−|B|} ("The proof in [GSV18] further shows that the probability of the fixing under D is ≥ 2^{−|B|}", p.6); reason: the conjunction implies the printed lemma; Theorem 1's proof uses the extra clause
--   - encoding: v ∈ {0,1}^B; D uniform on A; c-notation → v : Fin n → Bool read on B only; D = U conditioned on A; one c > 0 before all objects; reason: same instances
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 9, p.6 (from [GSV18, Lemma 3.14])

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
set_option autoImplicit false

namespace SamplingAC0

/-- **Lemma 9 (fixed-set lemma [GSV18, Lemma 3.14]) with the fixing probability.** Riazanov–Viola,
*Sampling Tools and the Power of AC0*, STOC 2027 submission (manuscript sha256 99c33d30…), Lemma 9,
p.6: "Let D be uniform on a set A ⊆ {0, 1}^n of size at least 2^{n−a}, and let U be uniform on
{0, 1}^n. Then for any η > 0 and s there is B ⊆ [n] and v ∈ {0, 1}^B, with |B| ≤ cas/η, such
that, writing D′ = (D | D_B = v) and R = (U | U_B = v), every decision tree T of depth ≤ s
satisfies ∆(T(D′), T(R)) ≤ η. The proof in [GSV18] further shows that the probability of the
fixing under D is ≥ 2^{−|B|}."

**Formalization Note.** `D` is the uniform distribution conditioned on `A`; `v` is given as a full
assignment of which only the coordinates in `B` matter; decision trees may have any finite output
type (a Boolean-output tree is a special case); depth `≤ s` is `MakesAtMost s`. The absolute
constant `c` comes before all objects. The fixing-probability clause is part of the statement
(the proof of Theorem 1 uses it). -/
theorem lemma_9 : ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (A : Finset (Fin n → Bool)) (a : ℝ),
    (2 : ℝ) ^ ((n : ℝ) - a) ≤ (A.card : ℝ) → ∀ η : ℝ, 0 < η → ∀ s : ℕ,
    ∃ (B : Finset (Fin n)) (v : Fin n → Bool),
      (B.card : ℝ) ≤ c * a * s / η ∧
      pr (condOn (unif (Fin n)) (A : Set (Fin n → Bool))) {x | ∀ j ∈ B, x j = v j}
        ≥ (2 : ℝ) ^ (-(B.card : ℝ)) ∧
      ∀ (β : Type) [Fintype β] (T : QAlgorithms.DecisionTree (Fin n) Bool β), T.MakesAtMost s →
        tvDist
          ((condOn (condOn (unif (Fin n)) (A : Set (Fin n → Bool))) {x | ∀ j ∈ B, x j = v j}).map
            T.eval)
          ((condOn (unif (Fin n)) {x | ∀ j ∈ B, x j = v j}).map T.eval) ≤ η := by sorry

end SamplingAC0
