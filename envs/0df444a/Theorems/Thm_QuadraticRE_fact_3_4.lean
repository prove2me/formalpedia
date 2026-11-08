-- Prove2me | Theorems.Thm_QuadraticRE_fact_3_4
-- name    : QuadraticRE.fact_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:17:50.006109+00:00
-- url     : https://prove2.me/theorems/d047b8b3-ad54-4339-bb55-0372e647385e
-- title:
--   Fact 3.4 — perfect degree-three encodings of mod-2 branching programs
-- statement:
--   There are a universal constant $K$, a polynomial $Q$ and one encoding construction such that for every branching program $P$ on $N$ inputs with $k$ vertices, computing $g:\{0,1\}^N\to\{0,1\}$, with total size $\sigma=k+N+1$:
--
--   1. the construction gives a perfectly correct, perfectly private randomized encoding of $g$;
--   2. its tape and output lengths are at most $K\sigma^2$, and its simulator uses at most $Q(\sigma)$ uniform coins;
--   3. every monomial of its description contains at most one input variable and at most two tape variables;
--   4. the description, the decoder and the simulator are constructed, and encoding, decoding and simulation are carried out, by fixed polynomial-time machines.
--
--   The paper cites this to [IK00, IK02, AIK06b]; Theorem 4.12 starts from it.
--
--   Differences from the source:
--   - reading: can be constructed in time polynomial in σ, and encoding, decoding and simulation also take time polynomial in σ → one fixed machine of Mathlib's Turing.TM2ComputableInPolyTime, from the bit encoding of the input (all numbers in unary) to the bit encoding of the output, in time polynomial in the input length; reason: Definition 3.7 gives no machine model; the length lemma of the verification file shows the encoded parameters have length between σ+λ and a fixed polynomial in σ+λ (paper.md decision 2)
--   - reading: randomness and output lengths O(σ²) → tape and output lengths at most K·σ², one universal K; reason: the constant of an O(·) is uniform over all programs
--   - encoding: a randomized simulator → a deterministic map on its input and τ uniform coins, with τ at most a fixed polynomial in σ; reason: Definition 3.7: random tapes consist of independent uniform bits and have polynomially bounded length
--   - encoding: g : {0,1}^N → {0,1} → g as a map to F₂^1; reason: one output bit; same function
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), Fact 3.4, p.14

import Mathlib
import Definitions.Def_QuadraticRE_IsRE
import Definitions.Def_QuadraticRE_Construction

namespace QuadraticRE

/-- Fact 3.4 of Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.14 (cited there to [IK00, IK02, AIK06b]): perfect degree-three encodings of
branching programs. The parameter is one program `P` on `N` inputs, whose total size is `σ = k + N + 1`
by the definition of p.14.

**Formalization Note.** One universal `K`, one polynomial `Q` and four machines, chosen before `P`. The
output `{0,1}` is `Fin 1 → F₂`. The simulator runs on uniform coins, as polynomially many as Definition
3.7 says. `g` is computed by counting paths, not by a determinant. -/
theorem fact_3_4 :
    ∃ (K : ℕ) (Q : Polynomial ℕ)
      (C : Construction (Par := Σ N, BP N) (fun p => p.1) (fun _ => 1)),
      (∀ p : Σ N, BP N,
        IsRE (fun (x : Fin p.1 → F2) (_ : Fin 1) => p.2.eval x) (C.desc p).eval 0 0
          (C.dec p) (fun y => law (C.sim p y)) ∧
        C.ρ p ≤ K * (p.2.k + p.1 + 1) ^ 2 ∧
        C.ℓ p ≤ K * (p.2.k + p.1 + 1) ^ 2 ∧
        C.τ p ≤ Q.eval (p.2.k + p.1 + 1) ∧
        ∀ i, ∀ m ∈ (C.desc p).coords i,
          m.countP (fun v => v.isLeft) ≤ 1 ∧ m.countP (fun v => v.isRight) ≤ 2) ∧
      C.IsPolyTime encBP := by sorry

end QuadraticRE
