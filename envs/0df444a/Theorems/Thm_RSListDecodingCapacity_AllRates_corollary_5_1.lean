-- Prove2me | Theorems.Thm_RSListDecodingCapacity_AllRates_corollary_5_1
-- name    : RSListDecodingCapacity.AllRates.corollary_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:38.935869+00:00
-- url     : https://prove2.me/theorems/ff47dc1d-f874-4662-850a-f946e2a64371
-- title:
--   Corollary 5.1 — deterministic list decoding of Reed–Solomon codes up to capacity at every constant rate
-- statement:
--   For every rate $R\in(0,1)$ and slack $\delta\in(0,1)$ there are a constant $C>0$, one deterministic algorithm and exponents $D_t,D_\ell$ (all depending only on $R,\delta$) such that the following holds. Let $n\ge k\ge1$ with $k/n\le R$, let $q$ be any prime with $q\ge Cn$, let $\alpha_1,\dots,\alpha_n\in\mathbb F_q$ be distinct evaluation points and $(y_1,\dots,y_n)\in\mathbb F_q^n$ any received word. Then the algorithm outputs, in at most $q^{D_t}$ steps, the list of all univariate polynomials $P\in\mathbb F_q[X]$ of degree less than $k$ such that the agreement between $(P(\alpha_1),\dots,P(\alpha_n))$ and $(y_1,\dots,y_n)$ is at least $(R+\delta)n$, each exactly once. Furthermore, the length of this list is at most $q^{D_\ell}$.
--
--   That is, Reed–Solomon codes of any constant rate over prime fields of linear size can be list decoded deterministically up to radius $1-R-\delta$, arbitrarily close to list-decoding capacity, in time and with list size $q^{O_{R,\delta}(1)}$, for arbitrary evaluation sets. The statement includes every $n$ (not only large $n$) and every $\delta\in(0,1)$; when $R+\delta>1$ the list is empty.
--
--   **Formalization Note** The algorithm is a multi-stack Turing machine over the Boolean alphabet whose time is its step count (`HMBinPacking.OutputsWithin`), started on the binary encoding of $n,k,q,A=\lceil(R+\delta)n\rceil,\alpha,y$. Since $q\ge2$, a bound $q^{O_{R,\delta}(1)}$ is a bound $q^{D}$ with $D$ depending only on $R,\delta$.
--
--   Differences from the source:
--   - reading: for any α and y, there is a deterministic algorithm which outputs … in q^O_{R,δ}(1) time → one Turing machine M and exponents D_t, D_ℓ chosen with C before n, k, q, α, y; reason: with the algorithm chosen after α and y the statement would be trivial (output a hard-coded list); the intended and stronger reading is one algorithm for all inputs, as in Theorem 4.1
--   - encoding: real parameters R, δ and agreement threshold (R+δ)n → R, δ fixed in the machine; input n, k, q, A = ⌈(R+δ)n⌉, α, y in binary; reason: a real number is not a finite input; agreement ≥ (R+δ)n is equivalent to agreement ≥ ⌈(R+δ)n⌉
--   - encoding: unspecified machine model, q^O_{R,δ}(1) time and list size → Turing.TM2ComputableAux Bool Bool, at most q^(D_t) steps, at most q^(D_ℓ) entries, output the coefficient vectors of length k; reason: q ≥ 2, so multiplicative constants are absorbed into the exponent; such bounds are invariant under polynomial simulations between machine models
-- source:
--   Joshua Brakensiek, Yeyuan Chen, Aaron Putterman, Zihan Zhang, Kai Zhe Zheng, Algorithmic List Decoding of Reed–Solomon Codes up to Capacity, STOC 2027 submission #565 (October 2026), p.28, Corollary 5.1 (Formal Version of Corollary 1.2)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

open Polynomial

namespace RSListDecodingCapacity.AllRates

/-- **Corollary 5.1 (Formal Version of Corollary 1.2)** (Brakensiek–Chen–Putterman–Zhang–Zheng,
STOC 2027 submission #565, p.28). For every rate `R ∈ (0, 1)` and slack `δ ∈ (0, 1)` there are a
constant `C > 0`, one deterministic algorithm `M` (a multi-stack Turing machine) and exponents
`D_t, D_ℓ` such that: for all `n ≥ k ≥ 1` with `k/n ≤ R`, every prime `q ≥ C n`, all distinct
`α₁, …, αₙ ∈ 𝔽_q` and every `y ∈ 𝔽_qⁿ`, started on `n, k, q, A = ⌈(R + δ)n⌉, α, y`, `M` outputs
within `q^{D_t}` steps the list of all `P ∈ 𝔽_q[X]` of degree less than `k` whose agreement with `y`
is at least `(R + δ)n`, each once; the list has at most `q^{D_ℓ}` entries. -/
theorem corollary_5_1 :
    ∀ R δ : ℝ, 0 < R → R < 1 → 0 < δ → δ < 1 →
      ∃ C : ℝ, 0 < C ∧ ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ Dt Dl : ℕ,
        ∀ n k : ℕ, 1 ≤ k → k ≤ n → (k : ℝ) / n ≤ R →
        ∀ q : ℕ, q.Prime → C * n ≤ (q : ℝ) →
        ∀ α : Fin n → ZMod q, Function.Injective α → ∀ y : Fin n → ZMod q,
          ∃ L : List (ZMod q)[X], L.Nodup ∧
            (∀ P : (ZMod q)[X], P ∈ L ↔ P ∈ listDecodingSet k α y ((R + δ) * n)) ∧
            HMBinPacking.OutputsWithin M (encDecodingInput k ⌈(R + δ) * n⌉₊ α y)
              (encPolyList k L) (q ^ Dt) ∧
            L.length ≤ q ^ Dl := by sorry

end RSListDecodingCapacity.AllRates
