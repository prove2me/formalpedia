-- Prove2me | Theorems.Thm_QMAvsQCIP_lemma_3
-- name    : QMAvsQCIP.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:11.59878+00:00
-- url     : https://prove2.me/theorems/a639b705-b609-41dc-b7fe-be380123659b
-- title:
--   Lemma 3 — public coins and perfect completeness in the classical query model
-- statement:
--   There is a fixed polynomial $p$ such that for every randomized classical query verifier $V$ (finite query domain $Z$ with queries of length $L$, $k$ random bits, at most $R$ rounds of $\ell$-bit messages and at most $T$ queries) there is a public-coin verifier $V'$ over the same domain, with all of its queries after the last prover reply, whose rounds, message length, number of queries, communication and random bits are at most $p(R+\ell+k+T+L)$, such that for every oracle $O$:
--
--   1. **Completeness.** If $\Pr[\langle P^O,V^O\rangle=\mathrm{ACCEPT}]\ge2/3-1/100$ for some prover $P$, then some deterministic prover $P'$ has $\Pr[\langle P'^O,V'^O\rangle=\mathrm{ACCEPT}]=1$.
--   2. **Soundness.** If $\max_{P^*}\Pr[\langle P^{*O},V^O\rangle=\mathrm{ACCEPT}]\le1/3+1/100$, then $\max_{P^*}\Pr[\langle P^{*O},V'^O\rangle=\mathrm{ACCEPT}]\le1/3$.
--
--   The construction depends only on $V$ and its bounds, and the bounds grow polynomially independently of local running time and advice. The lemma is the Goldwasser–Sipser and Fürer et al. transformations in the query complexity model.
--
--   **Formalization Note** Query length $L$ means $|Z|\le2^L$. "$\max_{P^*}\ldots\le c$" is "$\ldots\le c$ for every $P^*$".
--
--   Differences from the source:
--   - encoding: provers (arbitrary) → deterministic transcript functions; reason: Lemma 1(3), deterministic strategies attain the maximum acceptance
--   - encoding: bounds on rounds, communication, random bits and number and length of queries, increased polynomially → one polynomial of the sum $R+\ell+k+T+L$ bounding the new rounds, message length, queries, communication $2R'\ell'+1$ and random bits $R'\ell'$; reason: every polynomial bound in several nonnegative variables is bounded by a polynomial of their sum, and the communication $2R\ell+1$ of $V$ is bounded by a polynomial of $R+\ell$
--   - encoding: rounds and message lengths → fixed message length $\ell$ in both directions, at most $R$ rounds on every path; reason: padding (Section 5, p.23)
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Lemma 3, p.23

import Definitions.Def_QMAvsQCIP_cAccept
import Definitions.Def_QMAvsQCIP_pcAccept
import Definitions.Def_QMAvsQCIP_CTree_QueriesLE

set_option autoImplicit false

namespace QMAvsQCIP

/-- **Lemma 3 (Public coins and perfect completeness).** There is a fixed polynomial `p` such that
for every classical query verifier `V` (query domain `Z` with queries of length `L`, i.e.
`|Z| ≤ 2^L`; `k` random bits; at most `R` rounds of `ℓ`-bit messages and at most `T` queries on
every path) there is a public-coin verifier `V′` over the same domain, with all queries after the
last prover reply, whose rounds `R′`, message length `ℓ′`, query bound `T′`, communication
`2R′ℓ′ + 1` and random bits `R′ℓ′` are at most `p(R + ℓ + k + T + L)`, such that for every oracle
`O`:
1. **Completeness.** If some prover makes `V^O` accept with probability `≥ 2/3 − 1/100`, then some
   deterministic prover makes `V′^O` accept with probability `1`.
2. **Soundness.** If every prover makes `V^O` accept with probability `≤ 1/3 + 1/100`, then every
   prover makes `V′^O` accept with probability `≤ 1/3`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Lemma 3, p.23 (PDF p.26).

**Formalization Note.** `V′` is chosen from `V` (and its bounds) before the oracle: "The
construction depends only on V and its bounds". The polynomial `p` is chosen before everything:
"These bounds increase polynomially, independently of local running time and advice length,
even when the given bounds are arbitrary finite quantities." Provers are deterministic; for a
fixed oracle the honest `P′` may be chosen after `P`. "max_{P*} acc ≤ c" is written as
"acc ≤ c for every `P*`" (the two are equivalent). -/
theorem lemma_3 :
    ∃ p : Polynomial ℕ, ∀ (Z : Type) [Fintype Z] [DecidableEq Z] (ℓ R T L : ℕ)
      (V : CVerifier Z ℓ), Fintype.card Z ≤ 2 ^ L →
      (∀ c, CTree.RoundsLE R (V.tree c)) → (∀ c, CTree.QueriesLE T (V.tree c)) →
      ∃ (ℓ' T' : ℕ) (V' : PCVerifier Z ℓ'),
        (∀ a b, CTree.QueriesLE T' (V'.dec a b)) ∧
        V'.R + ℓ' + T' + (2 * V'.R * ℓ' + 1) + V'.R * ℓ' ≤ p.eval (R + ℓ + V.k + T + L) ∧
        ∀ O : Z → Bool,
          ((∃ P : BBProver ℓ, (2 : ℝ) / 3 - 1 / 100 ≤ cAccept V O P) →
            ∃ P' : BBProver ℓ', pcAccept V' O P' = 1) ∧
          ((∀ P : BBProver ℓ, cAccept V O P ≤ (1 : ℝ) / 3 + 1 / 100) →
            ∀ P : BBProver ℓ', pcAccept V' O P ≤ (1 : ℝ) / 3) := by sorry

end QMAvsQCIP
