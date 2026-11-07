-- Prove2me | Theorems.Thm_RGMISFast_eq_29
-- name    : RGMISFast.eq_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:29:42.768872+00:00
-- url     : https://prove2.me/theorems/4636302b-a16e-4f7e-b812-f91253a1fb91
-- title:
--   Eq. (29): $\Pr[B_A\mid F_{a/2}]\le 1\{A\subseteq V(G_{a/2})\}\Pr[E_a(A)\mid F_{a/2}]e^{-L}\gamma(a)^{|A|}$
-- statement:
--   Let $G$ be a finite simple graph with root $u^*$, let $L\ge8$, $m\ge1$, $a=a_m$, and let $A$ be a root-connected set. Let $B_A$ be either the growth event $|\Gamma_{a,ca}(A)|>2S(A,a)+L$ or a boundary event $K_{m,i}(A)>32c^{1+m-i}(2S(A,a)+L)$ with $0\le i<m$, and let $E_a(A)=\{r(v)\ge a\ \forall v\in A\}$. Conditionally on $F_{a/2}$ (the ranks below $a/2$),
--   $$
--   \Pr[B_A\mid F_{a/2}]\le \mathbf 1\{A\subseteq V(G_{a/2})\}\Pr[E_a(A)\mid F_{a/2}]\,e^{-L}\gamma(a)^{|A|}\le \mathbf 1\{A\subseteq V(G_{a/2})\}\,e^{-L}\gamma(a)^{|A|}. \tag{29}
--   $$
--
--   Summed over root-connected sets with Lemma 5.2, this gives Lemma 3.1.
--
--   **Formalization Note** Conditioning on $F_{a/2}$ is the explicit law in which the revealed ranks (below $a/2$) of a history $r_0$ are fixed and all other ranks are independent $a/2+\mathrm{Exp}(1)$; the statement holds for every history. $\mathbf 1\{A\subseteq V(G_{a/2})\}$ is computed from the history. Both events (the boundary event for every $i<m$) and both inequalities are stated.
--
--   Differences from the source:
--   - reading: Pr[· | F_{a/2}], a conditional probability → the measure under `condLaw r₀ (a/2) ∅ _` for every history r₀ (revealed ranks fixed, others i.i.d. a/2 + Exp(1)); reason: the explicit conditional law stated on p.18 and used by the proof; holding for every history is the pointwise form of the conditional bound
--   - generalization: a = a_m with 1 ≤ m ≤ M → a = a_m for every m ≥ 1; reason: the bound uses only 0 < a_m ≤ a₀ and i < m; restricting to m ≤ M gives the printed range
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), Proof of Lemma 3.1, eq. (29), p.25 (PDF p.27)

import Mathlib
import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_gammaA
import Definitions.Def_RGMISFast_condLaw

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace RGMISFast

/-- Eq. (29) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy MIS Is Fast at Every Node*,
STOC 2027 submission (manuscript sha256 e93cdfec…), Proof of Lemma 3.1, p.25): fix `a = a_m`, `m ≥ 1`, and a root-connected `A`, and
let `B_A` be either of the events `|Γ_{a,ca}(A)| > 2S(A, a) + L` or
`K_{m,i}(A) > 32c^{1+m−i}(2S(A, a) + L)` (`0 ≤ i < m`). Conditionally on `F_{a/2}`,
`Pr[B_A | F_{a/2}] ≤ 1{A⊆V(G_{a/2})} Pr[E_a(A) | F_{a/2}] e^{−L}γ(a)^{|A|} ≤ 1{A⊆V(G_{a/2})} e^{−L}γ(a)^{|A|}`,
where `E_a(A) = {r(v) ≥ a for every v ∈ A}`.

**Formalization Note** The conditional probability given `F_{a/2}` is the explicit law
`condLaw r₀ (a/2) ∅ _` for an arbitrary history `r₀` (revealed ranks below `a/2` fixed, all others
i.i.d. `a/2 + Exp(1)`; no prescribed set), and the statement holds for every history. The
indicator `1{A ⊆ V(G_{a/2})}` is computed from the history. `L ≥ 8`. Both events (the boundary
event for every `i < m`) and both inequalities are stated. -/
theorem eq_29 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (L : ℝ) (hL : 8 ≤ L) (m : ℕ) (hm : 1 ≤ m) (r₀ : V → ℝ)
    (hr₀ : IsHistory r₀ (am m / 2)) (A : Finset V) (hA : IsRootConnected G u A) :
    (condLaw r₀ (am m / 2) ∅ (fun _ => 0)
        {r | 2 * S r A (am m) + L < ((GammaAB G r (am m) ((c * am m : ℝ) : WithTop ℝ) A).card : ℝ)} ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ∧
      (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
          (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
            ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card)) ∧
    ∀ i : ℕ, i < m →
      condLaw r₀ (am m / 2) ∅ (fun _ => 0)
          {r | 32 * c ^ (1 + m - i) * (2 * S r A (am m) + L) < (Kmi G r m i A : ℝ)} ≤
            (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
                ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ∧
        (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              condLaw r₀ (am m / 2) ∅ (fun _ => 0) {r | ∀ v ∈ A, am m ≤ r v} *
                ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) ≤
            (if ActiveAt G r₀ (am m / 2) A then 1 else 0) *
              ENNReal.ofReal (Real.exp (-L) * gammaA (am m) ^ A.card) := by sorry

end RGMISFast
