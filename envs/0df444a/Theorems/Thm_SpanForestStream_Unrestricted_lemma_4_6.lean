-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_4_6
-- name    : SpanForestStream.Unrestricted.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:47.019183+00:00
-- url     : https://prove2.me/theorems/f48a60bf-673f-4b3c-bb52-fefa1c5461df
-- title:
--   Lemma 4.6 — sparse perturbed universal relation: I(S; M | T) = Ω(L log(2 + m/L) log(U/m))
-- statement:
--   Fix a constant $K_0\ge 0$. There are constants $c_0,C_0>0$ and a sufficiently small $\beta_0>0$, allowed to depend on $K_0$, as follows. Put $L=\ln(1/\beta)$ and suppose $0<\beta<\beta_0$, $m\ge L$, $U\ge C_0m$. There is a distribution $D=D(U,m,\beta)$ on pairs $T\subsetneq S\subseteq[U]$ with $|S|=m$ such that the following holds. Suppose a distribution $D'$ of $(S,T)$ and a generalized one-way protocol (message $M$ drawn from $(S,T)$, output $O$ drawn from $(M,T)$, so $O\leftrightarrow(M,T)\leftrightarrow S$) have error at most $\beta$ for the universal relation under $D'$, and
--   $$D_{\mathrm{KL}}(D'[S]\,\|\,D[S])\le K_0,\quad \mathbb E_{s\sim D'[S]}D_{\mathrm{KL}}(D'[T\mid S=s]\,\|\,D[T\mid S=s])\le\eta,$$
--   $$\mathbb E_{t\sim D'[T]}D_{\mathrm{KL}}(D'[S\mid T=t]\,\|\,D[S\mid T=t])\le\eta,\quad I(M;T\mid S)\le\eta,\quad \eta\le c_0\beta^2.$$
--   Then, for an absolute constant $c>0$,
--   $$I(S;M\mid T)\ge c\,L\,\log_2(2+m/L)\,\log_2(U/m).$$
--
--   This is the single-coordinate information bound that the coordinate reduction (Lemma 4.5) feeds into.
--
--   Differences from the source:
--   - reading: Ω(·) after 'Fix a constant K0'; only c0, C0, β0 are said to depend on K0 → the Ω-constant c is absolute, quantified before K0; reason: the stronger reading: App. B.4 says constants are absolute unless indicated, and its proof absorbs the K0 terms into C0
--   - encoding: L = ln(1/β), other logarithms → Real.log (natural) for L as printed; log₂ elsewhere; reason: App. A: binary unless written ln
--   - encoding: the protocol's output and error → output in Option [U] (none = failure symbol); error = Pr under D' that the output is not in S \ T; reason: the universal relation
--   - encoding: the constant K0 and η → K0 ≥ 0 and η real; divergences and informations in [0,∞]; reason: values of KL and information are nonnegative
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), pp. 30–31 (PDF 33–34), Lemma 4.6

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info
import Definitions.Def_SpanForestStream_Unrestricted_Protocols

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Lemma 4.6 (sparse perturbed universal relation): there is an absolute `c > 0` such that for
every `K₀ ≥ 0` there are `c₀, C₀, β₀ > 0` (depending on `K₀`) such that for `0 < β < β₀`,
`L = ln(1/β) ≤ m` and `U ≥ C₀ m` there is a law `D` on pairs `T ⊊ S ⊆ [U]` with `|S| = m`, for which
every input law `D'` and generalized one-way protocol with error at most `β` and the four
perturbation bounds with `η ≤ c₀ β²` has `I(S; M | T) ≥ c L log₂(2 + m/L) log₂(U/m)`. -/
theorem lemma_4_6 :
    ∃ c : ℝ, 0 < c ∧ ∀ K₀ : ℝ, 0 ≤ K₀ →
      ∃ c₀ C₀ β₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧ 0 < β₀ ∧
        ∀ (β : ℝ) (m U : ℕ), 0 < β → β < β₀ → Real.log (1 / β) ≤ m → C₀ * m ≤ U →
        ∃ D : PMF (Finset (Fin U) × Finset (Fin U)),
          (∀ st ∈ D.support, st.2 ⊂ st.1 ∧ st.1.card = m) ∧
          ∀ {Msg : Type} (D' : PMF (Finset (Fin U) × Finset (Fin U)))
            (msg : Finset (Fin U) → Finset (Fin U) → PMF Msg)
            (out : Msg → Finset (Fin U) → PMF (Option (Fin U))) (η : ℝ),
            probOf (genJoint D' msg out) {ω | ¬ URSolves ω.1.1 ω.1.2 ω.2.2} ≤
                ENNReal.ofReal β →
            klBits (D'.map Prod.fst) (D.map Prod.fst) ≤ ENNReal.ofReal K₀ →
            avgCondKL D' D Prod.fst Prod.snd ≤ ENNReal.ofReal η →
            avgCondKL D' D Prod.snd Prod.fst ≤ ENNReal.ofReal η →
            condMutualInfo (genJoint D' msg out) (fun ω => ω.2.1) (fun ω => ω.1.2)
                (fun ω => ω.1.1) ≤ ENNReal.ofReal η →
            η ≤ c₀ * β ^ 2 →
            ENNReal.ofReal (c * Real.log (1 / β) * Real.logb 2 (2 + m / Real.log (1 / β)) *
                Real.logb 2 (U / m)) ≤
              condMutualInfo (genJoint D' msg out) (fun ω => ω.1.1) (fun ω => ω.2.1)
                (fun ω => ω.1.2) := by sorry

end SpanForestStream.Unrestricted
