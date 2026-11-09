-- Prove2me | Theorems.Thm_QMAvsQCIP_theorem_7
-- name    : QMAvsQCIP.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:53:26.349436+00:00
-- url     : https://prove2.me/theorems/3dd0778f-f688-4a21-99f1-4fd9908601a0
-- title:
--   Theorem 7 — classical-query simulation: $|\Pr[\langle P^*,V^{O_F}\rangle]-\Pr[\langle P^*,V'^{O_F}\rangle]|\le\epsilon+g(F)$
-- statement:
--   Let $V$ be a quantum verifier with unrestricted finite local computation exchanging classical messages, with finite query domain $X$ and finite bounds $r,N,c,\ell$ on its rounds, queries, transcript length (including the final decision) and query length, $r,N\ge1$. For every integer $t\ge1$ and $0<\epsilon<1$ there are a randomized classical verifier $V'$ and an oracle-free randomized decoder $\mathrm{Dec}$, depending only on $V,t,\epsilon$, such that $V'$ has the same rounds and message lengths, makes at most $M=\mathrm{poly}(r,N,t,\ell,1/\epsilon)$ classical queries and uses $\mathrm{poly}(r,N,c,t,\ell,1/\epsilon)$ random bits, and for every $F\subseteq X$ and every prover $P^*$, with $O_F$ the membership oracle of $F$,
--   $$
--   \Big|\Pr[\langle P^{*O_F},V^{O_F}\rangle=\mathrm{ACCEPT}]-\Pr[\langle P^{*O_F},V'^{O_F}\rangle=\mathrm{ACCEPT}]\Big|\le\epsilon+g(F), \tag{26}
--   $$
--   where, with $\omega$ the decoder's shared random tape,
--   $$
--   g(F)=\Pr_\omega\Big[\exists\pi\in\{0,1\}^c,\ I\in\binom{[M]}{t}:\ \mathrm{Dec}(\pi,I,\omega)\in\binom Ft\Big]. \tag{25}
--   $$
--
--   The simulation replaces the verifier's superposition queries by polynomially many classical ones, at a cost controlled by how well a short message can describe $t$ elements of $F$; with incompressibility (Corollary 2) it yields Lemma 6.
--
--   **Formalization Note** $\mathrm{poly}(\ldots)$ is a fixed polynomial of the sum of the parameters, chosen before $V$. Query length $L$ means $|X|\le2^L$. The paper's $N$ bounds the queries per round; here $N$ bounds all queries of $V$. "The message $(\pi,I)$ has length $s=c+t\lceil\log_2M\rceil$" is the length of the encoding of $(\pi,I)$ by $\pi$ and the increasing list of the indices in $I$, and is not a separate clause.
--
--   Differences from the source:
--   - encoding: $N$ a bound on queries per round → $N$ a bound on the total number of queries; reason: the verifier has at most $r+1$ query phases, so the two hypotheses are interchangeable up to the polynomial $p_M$, which is existential
--   - encoding: $\mathrm{poly}(r,N,t,\ell,1/\epsilon)$ → $p(r+N+t+L+\lceil1/\epsilon\rceil)$ for a fixed polynomial $p$; reason: a polynomial bound in several nonnegative variables is bounded by a polynomial of their sum
--   - encoding: query length $\ell$ after padding → $|X|\le2^L$; reason: padded queries of length $L$ are an injection of $X$ into $\{0,1\}^L$
--   - encoding: shared random tape $\omega$ of the decoder → a probability space with measurable decoder outputs; reason: standing convention
--   - encoding: transcript length $c$ including the final decision → $2R\ell+1\le c$ for $R$ rounds of $\ell$-bit messages each way; reason: padding fixes rounds and message lengths (p.14), and the decision bit is counted (p.31)
--   - encoding: $V'$ preserves the rounds → $V'$ has at most $R$ rounds on every path of its query-and-message tree; reason: in the query model rounds are an upper bound (Definition 5: "over at most $r(\lambda)$ rounds"), and $V'$ keeps the message length $\ell$ by its type
--   - encoding: provers → deterministic transcript functions; reason: against classical messages every (randomized or quantum) prover strategy is a mixture of deterministic ones and both acceptance probabilities are linear in the mixture, so the bound for every deterministic prover gives it for every prover by convexity of $|\cdot|$
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Theorem 7, Eqs. (25)–(26), p.31

import Definitions.Def_QMAvsQCIP_qqAccept
import Definitions.Def_QMAvsQCIP_qqQueries
import Definitions.Def_QMAvsQCIP_cAccept
import Definitions.Def_QMAvsQCIP_CTree_RoundsLE
import Definitions.Def_QMAvsQCIP_CTree_QueriesLE

set_option autoImplicit false

namespace QMAvsQCIP

open MeasureTheory

/-- **Theorem 7 (Classical-query simulation).** There are fixed polynomials `p_M`, `p_R` with the
following property. Let `V` be a quantum query verifier exchanging classical messages, with
finite query domain `X` (queries of length `L` after padding, `|X| ≤ 2^L`), and bounds
`r, N ≥ 1` on its rounds and queries and `c` on its transcript length `2Rℓ + 1` (which includes
the final decision). For every integer `t ≥ 1` and `0 < ϵ < 1` there are
`M ≤ p_M(r + N + t + L + ⌈1/ϵ⌉)`, a randomized classical verifier `V′` with the same rounds and
message length, at most `M` classical queries and at most `p_R(r + N + c + t + L + ⌈1/ϵ⌉)` random
bits, and an oracle-free randomized decoder `Dec(π, I, ω)` (`π ∈ {0,1}^c`, `I` a set of indices in
`[M]`, `ω` its shared random tape), all depending only on `V`, `t`, `ϵ`, such that for every
`F ⊆ X` and every prover `P*`, with `O_F` the membership oracle of `F`,
`|Pr[⟨P*, V^{O_F}⟩ = ACCEPT] − Pr[⟨P*, V′^{O_F}⟩ = ACCEPT]| ≤ ϵ + g(F)`, where
`g(F) = Pr_ω[∃ π ∈ {0,1}^c, I ∈ ([M] choose t) : Dec(π, I, ω) ∈ (F choose t)]`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Theorem 7, p.31 (PDF p.34), Eqs. (25)–(26).

**Formalization Note.** `poly(r, N, t, ℓ, 1/ϵ)` is a polynomial of the sum of the parameters
(every polynomial bound in several nonnegative variables is bounded by one of their sum).
The paper's `N` bounds the queries per round; here `N` bounds all queries of `V`; the two are
interchangeable up to the polynomial (the verifier has `R + 1 ≤ r + 1` query phases). "The
message `(π, I)` has length `s = c + t⌈log₂ M⌉`" is the length of the encoding of the pair
`(π, I)` by `π` and the increasing list of the indices of `I`; it is not a separate clause. -/
theorem theorem_7 :
    ∃ pM pR : Polynomial ℕ, ∀ (X : Type) [Fintype X] [DecidableEq X] (V : QQVerifier X)
      (r N c L : ℕ), 1 ≤ r → 1 ≤ N → V.R ≤ r → qqQueries V ≤ N → 2 * V.R * V.ℓ + 1 ≤ c →
      Fintype.card X ≤ 2 ^ L →
      ∀ t : ℕ, 1 ≤ t → ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ (M : ℕ) (V' : CVerifier X V.ℓ),
          M ≤ pM.eval (r + N + t + L + ⌈1 / ε⌉₊) ∧
          (∀ coins, CTree.RoundsLE V.R (V'.tree coins)) ∧
          (∀ coins, CTree.QueriesLE M (V'.tree coins)) ∧
          V'.k ≤ pR.eval (r + N + c + t + L + ⌈1 / ε⌉₊) ∧
          ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω), IsProbabilityMeasure μ ∧
            ∃ Dec : (Fin c → Bool) → Finset (Fin M) → Ω → Finset X,
              (∀ π I T, MeasurableSet {ω | Dec π I ω = T}) ∧
              ∀ (F : Finset X) (P : BBProver V.ℓ),
                |qqAccept V (fun z => decide (z ∈ F)) P -
                    cAccept V' (fun z => decide (z ∈ F)) P| ≤
                  ε + (μ {ω | ∃ π I, I.card = t ∧ Dec π I ω ⊆ F ∧
                    (Dec π I ω).card = t}).toReal := by sorry

end QMAvsQCIP
