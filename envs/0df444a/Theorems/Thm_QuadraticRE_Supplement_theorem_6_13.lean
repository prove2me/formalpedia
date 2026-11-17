-- Prove2me | Theorems.Thm_QuadraticRE_Supplement_theorem_6_13
-- name    : QuadraticRE.Supplement.theorem_6_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:57:21.833207+00:00
-- url     : https://prove2.me/theorems/fbc5cabe-042b-4cf9-b228-c4180c5548f1
-- title:
--   Theorem 6.13 — statistical two-round client–server protocols for $n>2t$ with both errors at most $2^{-\lambda}$ and polynomial time and communication
-- statement:
--   Let $0\le t<n$ with $n>2t$, let $F$ be represented by mod-2 branching programs of total size $\sigma$ (including its input and output lengths) together with the assignment of its input bits to $m\ge1$ input clients, and let $\lambda\ge1$. Then $F$ has a protocol in the model of Definition 6.10 (input clients, an inputless receiver $D$, $n$ servers, one round of uploads and one round of replies, private channels only) with
--   $$\text{correctness error}\le2^{-\lambda}\qquad\text{and}\qquad\text{statistical privacy error against }A_t\le2^{-\lambda},$$
--   where $A_t$ is the class of coalitions consisting of any set of input clients, possibly $D$, and at most $t$ servers. One construction and one polynomial serve all parameters: the construction and all protocol and simulation algorithms run in time polynomial in $m+n+\sigma+\lambda$, and the total communication is at most a fixed polynomial in $m+n+\sigma+\lambda$.
--
--   The threshold $n>2t$ is optimal for general statistical computation (Lemma A.1 of the paper).
--
--   Differences from the source:
--   - encoding: finite nonempty tape, upload and reply sets → bit strings F₂^k of lengths chosen by the construction; reason: a protocol of this form is a protocol of Definition 6.10, so the existence claim is not weakened
--   - encoding: F represented by branching programs with the assignment of its input bits to the parties → a Rep with a map owner : Fin N → Fin m; client i's input is the bits it owns; reason: p.14: the representation specifies the assignment of input bits to parties
--   - encoding: the view of a coalition (inputs, complete tapes, received messages) → one tuple with a slot per party, none outside the coalition: client inputs and tapes, receiver tape and all replies, server tapes and all uploads they receive; reason: Definitions 3.5 and 6.4 and View_C of Lemma 6.12
--   - encoding: a randomized simulator → a deterministic map on τ(p) uniform coins, τ(p) independent of the coalition and output by the construction machine; reason: Definition 3.7; a simulator can always use the maximum coin count over coalitions
--   - reading: construction and all protocol and simulation algorithms run in time polynomial in m + n + σ + λ → fixed machines of Mathlib's Turing.TM2ComputableInPolyTime for the lengths, every upload, every reply, the decoder and the simulator, each on the unary encoding of the parameters followed by its data; reason: Definition 3.7 names no machine model; the encoded parameters have length polynomially related to m + n + σ + λ
--   - encoding: total communication polynomial in m + n + σ + λ → the sum of all upload and reply lengths is at most P(m + n + σ + λ) for one polynomial P chosen before the parameters; reason: uniform polynomial bound, as in Definition 3.7
--   - encoding: 2^{−λ} → (1/2)^λ; reason: Lean notation; same number
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Theorem 6.13, p.47; Definition 6.10, pp.43–44; class A_t, p.44

import Mathlib
import Definitions.Def_QuadraticRE_Supplement_CSConstruction

namespace QuadraticRE.Supplement

open QuadraticRE CSProtocol

/-- Theorem 6.13 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript
(sha256 0c94deae…), p.47: statistical client–server protocols under an honest majority.

There are one construction `K` and one polynomial `P` such that for every public parameter
`p = (rep, m, owner, n, t, 1^λ)` with `m ≥ 1`, `n > 2t` and `λ ≥ 1`, the protocol `K.prot p` of
Definition 6.10 for `F = p.F` has correctness error at most `2^{−λ}` and, with the simulator `K.sim p`,
statistical privacy error at most `2^{−λ}` against every coalition in `A_t`, and total communication
at most `P(m + n + σ + λ)`; the construction and all protocol and simulation algorithms are
polynomial-time machines.

**Formalization Note.** `2^{−λ}` is `(1/2)^λ`. Machine time is polynomial in the length of the encoded
input, which starts with the encoding of `p`, whose length is polynomially related to
`m + n + σ + λ`; the tapes and messages on the inputs have lengths output by the construction
machine, hence polynomially bounded. -/
theorem theorem_6_13 :
    ∃ (P : Polynomial ℕ) (K : CSConstruction),
      K.IsPolyTime ∧
      ∀ p : CSParam,
        (K.prot p).IsCorrect p.F ((1 / 2 : ℝ) ^ p.lam) ∧
        (K.prot p).IsPrivate p.F p.t ((1 / 2 : ℝ) ^ p.lam) (K.τ p) (K.sim p) ∧
        (K.prot p).comm ≤ P.eval (p.m + p.n + p.rep.size + p.lam) := by sorry

end QuadraticRE.Supplement
