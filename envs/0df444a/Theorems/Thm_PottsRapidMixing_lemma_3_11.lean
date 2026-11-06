-- Prove2me | Theorems.Thm_PottsRapidMixing_lemma_3_11
-- name    : PottsRapidMixing.lemma_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:55:57.946694+00:00
-- url     : https://prove2.me/theorems/34016579-9fee-41c1-b5e0-ac6b848014bb
-- title:
--   Lemma 3.11, p.21 — exponential tails under $Q$
-- statement:
--   Let $\Delta\ge3$, $0<s<1/d$, $R\ge1$, $0<\delta<\frac{1-ds}{16(1+\Delta b_R)^2}$ and $\eta>0$. There are constants $c_0,C_1,C_{\mathrm{tail}}>0$, depending only on $\Delta,R,s,\delta,\eta$, such that the following holds. Let $G$ be a graph on $n$ vertices of maximum degree $\Delta$ with $|E(G[U])|\le(1+\delta)|U|$ for every $U\subseteq V$ with $|U|\le\eta n$. Let $\nu$ be any distribution, in either case of Definition 3.6, where $R$ satisfies (3.1), resp. (3.6), at $s$, and let $Q$ be the law of Definition 3.7. Let $h$ be a history with $Q(\mathcal R_j=h)>0$ after which Algorithm 1 is at line 3, and let $\mathcal C$ be the component explored next. Then for every $m\ge1$,
--   $$Q(|\mathcal C|\ge m\mid\mathcal R_j=h)\le C_1e^{-2c_0m},\tag{3.19}$$
--   and for every integer $a\ge0$,
--   $$\mathbb E_Q\bigl[e^{c_0|\mathcal C|}\mathbf 1\{|\mathcal C|>a\}\mid\mathcal R_j=h\bigr]\le C_{\mathrm{tail}}e^{-c_0a}.\tag{3.20}$$
--
--   Under $Q$ every component has an exponential size tail, uniformly in the past of the exploration.
--
--   **Formalization Note** Both cases are in the one statement. The spin case has integer $q\ge2$, the edge case real $q\ge1$, each with $0<\beta<\beta_u$. Verification files show that all hypotheses hold at once for a concrete instance, with a history of positive $Q$-mass.
--
--   Differences from the source:
--   - encoding: M, the standing chain of §2 → M = M(r) with r of (2.1), rOf Δ q β; reason: §2, p.9 fixes these parameters
--   - encoding: β < β_u (or B < B_u), with β > 0 standing → 0 < β < β_u(q, T_Δ); reason: 0 < β is standing on pp.1, 9; B = e^β
--   - generalization: "maximum degree Δ" → degree at most Δ at every vertex; reason: the proof uses only the upper bound; a graph of maximum degree Δ satisfies it, so the statement specializes to the source
--   - generalization: δ, R, s are the constants of (3.18), (3.7) and Lemmas 3.4–3.5, with s ∈ (s_∞, 1/d) fixed on p.16 → 0 < s < 1/d, δ satisfies the first clause of (3.18), and R satisfies (3.1), resp. (3.6), at s, as hypotheses SpinSubcritical, EdgeSubcritical; reason: the lemma names them without restating them, and (3.7) is what ties R to s (paper.md R10); s > s_∞ is not required, and the page's s and the R of Lemmas 3.4–3.5 satisfy these hypotheses, so the statement specializes to the source
--   - encoding: the second clause of (3.18), ds^γ < 1 for a fixed γ → omitted; reason: the lemma does not use γ, and such a γ < 1 exists whenever ds < 1
--   - encoding: "the component that is explored next" after h → the component with index i, for the pass of line 3 with i finished components; reason: a history can pass line 3 several times, because isolated vertices need no test; the statement covers every pass, which p.24 uses
--   - reading: "q ≥ 1" in the edge case → q real, q ≥ 1; reason: as in Lemma 3.5 (paper.md R4)
-- source:
--   Blanca, Gheissari, Park, Zhang, Rapid mixing of Potts Glauber dynamics throughout uniqueness, arXiv:2610.42059, Lemma 3.11, (3.19), (3.20), p.21; (3.18), p.21

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_PottsRapidMixing_Threshold
import Definitions.Def_PottsRapidMixing_Cycles
import Definitions.Def_PottsRapidMixing_RecordLaws

open scoped Classical
open Filter Topology

namespace PottsRapidMixing

/-- **Lemma 3.11** (Blanca, Gheissari, Park, Zhang, arXiv:2610.42059, p.21). There are constants
`c₀, C₁, C_tail > 0`, depending only on `Δ`, `R`, `s`, `δ`, `η`, such that the following holds. Let `G` be a
graph on `n` vertices of maximum degree `Δ` with `|E(G[U])| ≤ (1 + δ)|U|` for every `|U| ≤ ηn`. For any
distribution `ν`, let `Q` be its law of records of Definition 3.7. Let `h` be a history with `Q(R_j = h) > 0`
after which Algorithm 1 is at line 3, and `C` the component explored next. Then for every `m ≥ 1`,
`Q(|C| ≥ m | R_j = h) ≤ C₁ e^{−2c₀m}`, (3.19), and for every integer `a ≥ 0`,
`E_Q[e^{c₀|C|} 1{|C| > a} | R_j = h] ≤ C_tail e^{−c₀a}`, (3.20).

**Formalization Note.** Both cases of Definition 3.6 are in this one statement. `δ` satisfies the first
clause of (3.18). Its second clause only fixes `γ`, which the lemma does not use, and holds for some `γ < 1`
whenever `ds < 1`. `R` and `s` are tied by (3.7): `R` satisfies (3.1), resp. (3.6), at `s`, which is what
`SpinSubcritical`, `EdgeSubcritical` say, and that hypothesis is a statement about `R`, not an added
assumption on `G`. The constants do not depend on `q`, `β`, `G`, `ν` or the orderings. -/
theorem lemma_3_11 (Δ : ℕ) (hΔ : 3 ≤ Δ) (s : ℝ) (hs0 : 0 < s) (hs : ((Δ : ℝ) - 1) * s < 1)
    (R : ℕ) (hR : 1 ≤ R) (δ : ℝ) (hδ0 : 0 < δ)
    (hδ : δ < (1 - ((Δ : ℝ) - 1) * s) / (16 * (1 + (Δ : ℝ) * bR Δ R) ^ 2))
    (η : ℝ) (hη : 0 < η) :
    ∃ c₀ C₁ Ctail : ℝ, 0 < c₀ ∧ 0 < C₁ ∧ 0 < Ctail ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V), (∀ v, G.degree v ≤ Δ) →
      (∀ U : Finset V, (U.card : ℝ) ≤ η * (Fintype.card V : ℝ) →
        (edgesIn G U : ℝ) ≤ (1 + δ) * (U.card : ℝ)) →
      ∀ ord : ExplOrder G,
        (∀ (q : ℕ) (β : ℝ), 2 ≤ q → 0 < β → β < betaU (q : ℝ) Δ →
          SpinSubcritical Δ q β (rOf Δ (q : ℝ) β) s R →
          ∀ ν : (V → Fin q) → ℝ, MarkovMixing.IsDist ν →
            ComponentTails ord R ν (spinLik β (rOf Δ (q : ℝ) β))
              (spinInner R β (rOf Δ (q : ℝ) β)) c₀ C₁ Ctail) ∧
        (∀ q β : ℝ, 1 ≤ q → 0 < β → β < betaU q Δ → EdgeSubcritical Δ (pOf β) q s R →
          ∀ ν : (G.edgeSet → Bool) → ℝ, MarkovMixing.IsDist ν →
            ComponentTails ord R ν edgeLik (edgeInner R (pOf β) q) c₀ C₁ Ctail) := by sorry

end PottsRapidMixing
