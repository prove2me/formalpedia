-- Prove2me | Theorems.Thm_RelQueryPTime_initial_tape_fo
-- name    : RelQueryPTime.initial_tape_fo
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:41:29.553711+00:00
-- url     : https://prove2.me/theorems/997aa563-6e22-4bfe-a178-42694930dc95
-- title:
--   Proof of Theorem 1 — the initial tape $M_0(c,p,a)$ is first order
-- statement:
--   Let $\sigma$ be a scheme, $r \ge 0$, $M$ a Turing machine with input alphabet $\{0,1\}$, and $K \ge 0$. Let $\ell$ be the number of possible cell contents. There is a first-order formula $M_0(\bar x, \bar p, \bar a)$ of relational calculus with $\le$, with $\bar x$ an $r$-tuple, $\bar p$ a $(K+1)$-tuple and $\bar a$ an $\ell$-tuple of variables, such that for every ordered database $B$ with $n$ elements and all tuples $\bar c$, $\bar p$, $\bar a$:
--   $$
--   B \models M_0(\bar c, \bar p, \bar a) \iff \bar a \text{ codes } \mathrm{Cell}_{M,\langle B,\bar c\rangle}\big(0,\ \mathrm{value}(\bar p) - n^K\big).
--   $$
--   That is, $M_0$ says that at time $0$ the cell numbered by $\bar p$ contains the symbol coded by $\bar a$, i.e. that the initial tape holds $\langle B, \bar c\rangle$.
--
--   **Formalization Note** Cell numbers are offset by $n^K$ so that cells to the left of the input, which Cook's two-way tape uses, are addressed. A cell content is coded by $\ell$ bits $[a_m \neq 0]$. Databases of every size are covered.
--
--   Differences from the source:
--   - reading: cell p is a (p a k-tuple, a one variable ranging over symbols) → cell number value(p) − n^K for a (K+1)-tuple p; the symbol coded by an ℓ-tuple a through the bits [a_m ≠ 0]; reason: Cook's two-way tape needs cells left of the input; the set of cell contents can be larger than the domain
--   - reading: some binary representation for c1…cr → each c_i one-hot (n bits with a single 1); reason: under positional binary the first-order M0 claimed by the page does not exist (bit 0 of c1 is the parity of its position, which FO(≤) does not define on linear orders); one-hot is a binary representation, and milestone encoding_robust shows P is unchanged
--   - generalization: M0 for the machine M and the exponent k of the proof → for every machine M with input alphabet {0,1} and every K; reason: the page's M and k are an instance
-- source:
--   N. Immerman, Relational Queries Computable in Polynomial Time (Extended Abstract), Proc. 14th ACM STOC, 1982, pp.147–152, doi:10.1145/800070.802187, proof of Theorem 1, p.149 ("First we must write the sentence M0(c,p,a) … we can write the first order sentence M0 saying that the input is correct.") (PDF p.3)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_RelQueryPTime_Syntax
import Definitions.Def_RelQueryPTime_Encoding
import Definitions.Def_RelQueryPTime_TupleValue
import Definitions.Def_RelQueryPTime_Machine

namespace RelQueryPTime

/-- The initial tape is first order (Immerman, *Relational Queries Computable in Polynomial Time*, STOC 1982, proof of Theorem 1, p.149: "First we must write the
sentence `M₀(c,p,a)` meaning that at time 0, cell p is a, i.e. that the initial input tape contains
`<B,c>`. … using `≤` and relation symbols `R₁ … R_k` we can write the first order sentence `M₀`
saying that the input is correct.").

For every scheme `σ`, arity `r`, Turing machine `M` with input alphabet `Bool` (embedded by `ι`)
and `K`, there is a first-order formula `M₀(x, p, a)` such that on every database `B` with `n`
elements, for every `r`-tuple `c`, every `(K+1)`-tuple `p` and every `ℓ`-tuple `a`
(`ℓ = symWidth M`): `B ⊨ M₀(c, p, a)` iff `a` codes the contents of cell number
`value(p) − n^K` at time `0` of the run of `M` on `⟨B, c⟩`.

**Formalization Note** Free variables: `x` = `0, …, r-1`, `p` = the next `K+1`, `a` = the last
`ℓ`. Cell numbers are offset by `n^K` so that cells left of the input are addressed. A symbol needs
two distinct elements to be coded in bits; for `n ≤ 1` the statement is still required. -/
theorem initial_tape_fo (σ : Schema) (r : ℕ) {Γ : Type} [Fintype Γ] (ι : Bool ↪ Γ)
    (M : CookPvsNP.TM Γ) (K : ℕ) :
    ∃ M₀ : Formula σ, M₀.IsFO ∧ M₀.fv ⊆ {i | i < r + (K + 1) + symWidth M} ∧
      ∀ (n : ℕ) (B : Database σ n) (c : Fin r → Fin n) (p : Fin (K + 1) → Fin n)
        (a : Fin (symWidth M) → Fin n),
        (M₀.query (r + (K + 1) + symWidth M) n B (Fin.append (Fin.append c p) a) ↔
          decodeSym M a =
            some (cell M ((enc B c).map ι) 0 ((tupleValue (K + 1) p : ℤ) - (n : ℤ) ^ K))) := by sorry

end RelQueryPTime
