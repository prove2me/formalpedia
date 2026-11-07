-- Prove2me | Theorems.Thm_SamplingAC0_claim_13
-- name    : SamplingAC0.claim_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:47:34.67341+00:00
-- url     : https://prove2.me/theorems/b718e31c-01f5-463d-9a14-578351779c15
-- title:
--   Claim 13 — $A=\mathbb P[h_\ell(Y)=0\mid g_i(X)\in\ell]\ge c$
-- statement:
--   There is an absolute constant $c>0$ such that for every $C>0$ there is $Q$ with the following property. Let $q=2^k\ge Q$, fix an encoding of $\mathbb F_q$, and let $f=(h,g)$ be a forest on $s$ input bits with the output positions of $R$, and $i\in[q]$, such that
--
--   - (C3) $\mathbb P_{\ell,U}[h_\ell(U)=0]\ge0.01$ for $U$ uniform and $\ell$ a uniform line, and
--   - (C4) $\Delta\bigl(g_i(U),U_{\mathbb F_q^2}\bigr)\le C\,q^{-1/16}$.
--
--   Let $X,Y$ be independent uniform inputs and $\ell$ a uniform line independent of both. Then
--
--   $$A=\mathbb P\bigl[h_\ell(Y)=0\mid g_i(X)\in\ell\bigr]\ \ge\ c .$$
--
--   In the proof of Theorem 10, $f$ is the restricted forest supplied by Lemma 12; the claim gives the main term of the lower bound on the probability that the output is invalid.
--
--   **Formalization Note** The conditional probability is multiplied out: $\mathbb P[h_\ell(Y)=0\wedge g_i(X)\in\ell]\ge c\,\mathbb P[g_i(X)\in\ell]$ (and $\mathbb P[g_i(X)\in\ell]=1/q$).
--
--   Differences from the source:
--   - generalization: the restricted forest f|ρ supplied by Lemma 12 ("Let us assume henceforth that f is restricted according to ρ") → every forest f on s bits satisfying (C3) and (C4), the latter with any constant C; reason: a restricted forest is a forest on its free bits and satisfies these hypotheses, so the statement specializes to the source's use
--   - encoding: "for sufficiently large q"; c-notation; A a conditional probability → ∃ c before C, ∃ Q(C), q = 2^k ≥ Q; the conditional multiplied out; (ℓ, X, Y) uniform on the product; reason: same instances
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Claim 13, p.10

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_lineDNF
import Definitions.Def_SamplingAC0_R
set_option autoImplicit false

namespace SamplingAC0

/-- **Claim 13 (`A ≥ c`).** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027
submission (manuscript sha256 99c33d30…), Claim 13, p.10: "A ≥ c.", where (p.10)
"A := P[h_ℓ(Y) = 0 | g_i(X) ∈ ℓ]" for independent uniform inputs `X, Y ∼ {0,1}^s` and a uniform
line `ℓ` independent of both; the claim is proved for sufficiently large `q` from (C3) and (C4) of
Lemma 12 for the (restricted) forest.

Stated for a forest `f` on `s` bits (the restricted forest of the proof is such a forest), with
hypotheses (C3) and (C4) for `f` itself, (C4) with any constant `C`.

**Formalization Note.** The conditional probability is multiplied out:
`P[h_ℓ(Y) = 0 ∧ g_i(X) ∈ ℓ] ≥ c · P[g_i(X) ∈ ℓ]`. The absolute constant `c` comes before `C`;
the threshold `Q` on `q` depends on `C` only. -/
theorem claim_13 : ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ, 0 < C → ∃ Q : ℕ, ∀ (enc : Encoding) (k : ℕ),
    Q ≤ 2 ^ k → ∀ (s : ℕ) (f : Forest s (ROut k)) (i : Fin (2 ^ k)),
    expect (PMF.uniformOfFintype (Line k))
        (fun ℓ => pr (unif (Fin s)) {x | (f (Sum.inl ℓ)).eval x = false}) ≥ 0.01 →
    tvDist ((unif (Fin s)).map (fun x => decodeOut enc (f.eval x) i))
        (PMF.uniformOfFintype (F k × F k)) ≤ C * ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 16) →
    pr (PMF.uniformOfFintype (Line k × (Fin s → Bool) × (Fin s → Bool)))
        {ω | (f (Sum.inl ω.1)).eval ω.2.2 = false ∧ onLine ω.1 (decodeOut enc (f.eval ω.2.1) i)}
      ≥ c * pr (PMF.uniformOfFintype (Line k × (Fin s → Bool) × (Fin s → Bool)))
        {ω | onLine ω.1 (decodeOut enc (f.eval ω.2.1) i)} := by sorry

end SamplingAC0
