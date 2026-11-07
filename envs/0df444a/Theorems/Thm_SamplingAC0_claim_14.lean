-- Prove2me | Theorems.Thm_SamplingAC0_claim_14
-- name    : SamplingAC0.claim_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:48:54.303068+00:00
-- url     : https://prove2.me/theorems/3b8b6d82-2806-4483-8578-80af3020d85e
-- title:
--   Claim 14 — $B=\mathbb P[h_\ell(U)\ne h_\ell(Y)\mid g_i(X)\in\ell]=o(1)$
-- statement:
--   For every $C>0$ and $\eta>0$ there is $Q$ with the following property. Let $q=2^k\ge Q$, fix an encoding of $\mathbb F_q$, and let $f=(h,g)$ be a forest of depth at most $q^{1/10}$ on $s$ input bits with the output positions of $R$, and $i\in[q]$, such that
--
--   - (C1) $f$ is average-$q^{5/4}$-Lipschitz, and
--   - (C4) $\Delta\bigl(g_i(U),U_{\mathbb F_q^2}\bigr)\le C\,q^{-1/16}$.
--
--   Let $X,Y$ be independent uniform inputs, $\ell$ a uniform line independent of both, and $U$ the hybrid of $X$ and $Y$ ($U_j=X_j$ if one of the $2k$ trees computing $g_i(X)$ queries $j$, else $U_j=Y_j$). Then
--
--   $$B=\mathbb P\bigl[h_\ell(U)\ne h_\ell(Y)\mid g_i(X)\in\ell\bigr]\ \le\ \eta .$$
--
--   That is, $B=o(1)$ as $q\to\infty$, uniformly in the forest. This is the crucial step of the proof of Theorem 10: the line tree $h_\ell$ rarely reads the bits that determine $g_i$, even conditioned on $g_i(X)\in\ell$.
--
--   **Formalization Note** The conditional probability is multiplied out: $\mathbb P[h_\ell(U)\ne h_\ell(Y)\wedge g_i(X)\in\ell]\le\eta\,\mathbb P[g_i(X)\in\ell]$.
--
--   Differences from the source:
--   - generalization: the restricted forest f|ρ supplied by Lemma 12 → every forest f on s bits of depth ≤ q^{1/10} satisfying (C1) and (C4), the latter with any constant C; reason: a restricted forest is a forest on its free bits and satisfies these hypotheses, so the statement specializes to the source's use
--   - reading: B = o(1) → for every η > 0 there is Q (depending on C and η only) with B ≤ η for all q = 2^k ≥ Q, uniformly in the encoding, s, f and i; reason: the stronger reading; the proof's bound o(1) + 2kd·q^{−1/4} is uniform
--   - encoding: B a conditional probability → the conditional multiplied out; (ℓ, X, Y) uniform on the product; reason: P[g_i(X) ∈ ℓ] = 1/q > 0
-- source:
--   Riazanov–Viola, Sampling Tools and the Power of AC0, STOC 2027 submission (manuscript sha256 99c33d30…), Claim 14, pp.10–11

import Mathlib
import Definitions.Def_SamplingAC0_Forest
import Definitions.Def_SamplingAC0_law
import Definitions.Def_SamplingAC0_tvDist
import Definitions.Def_SamplingAC0_Restriction
import Definitions.Def_SamplingAC0_AvgLipschitz
import Definitions.Def_SamplingAC0_lineDNF
import Definitions.Def_SamplingAC0_R
import Definitions.Def_SamplingAC0_hybrid
set_option autoImplicit false

namespace SamplingAC0

/-- **Claim 14 (`B = o(1)`).** Riazanov–Viola, *Sampling Tools and the Power of AC0*, STOC 2027
submission (manuscript sha256 99c33d30…), Claim 14, pp.10–11: "B = P[h_ℓ(U) ≠ h_ℓ(Y) | g_i(X) ∈ ℓ]
= o(1).", where `X, Y ∼ {0,1}^s` are independent uniform inputs, `ℓ` is a uniform line independent
of both, and `U` is the hybrid of `X` and `Y` (p.10): `U_j = X_j` if one of the `2k` trees
computing `g_i(X)` queries `j`, else `U_j = Y_j`.

Stated for a forest `f` on `s` bits of depth `≤ q^{1/10}` (the restricted forest of the proof is
such a forest), with hypotheses (C1) and (C4) of Lemma 12 for `f` itself, (C4) with any constant
`C`.

**Formalization Note.** "o(1)" as `q → ∞`: for every `η > 0` there is `Q` (depending on `C` and
`η` only) with `B ≤ η` for all `q = 2^k ≥ Q`, uniformly in the encoding, `s`, `f` and `i`. The
conditional probability is multiplied out. -/
theorem claim_14 : ∀ C : ℝ, 0 < C → ∀ η : ℝ, 0 < η → ∃ Q : ℕ, ∀ (enc : Encoding) (k : ℕ),
    Q ≤ 2 ^ k → ∀ (s : ℕ) (f : Forest s (ROut k)) (i : Fin (2 ^ k)),
    f.DepthLE (((2 : ℝ) ^ k) ^ ((1 : ℝ) / 10)) →
    AvgLipschitz f (Restriction.empty s) (((2 : ℝ) ^ k) ^ ((5 : ℝ) / 4)) →
    tvDist ((unif (Fin s)).map (fun x => decodeOut enc (f.eval x) i))
        (PMF.uniformOfFintype (F k × F k)) ≤ C * ((2 : ℝ) ^ k) ^ (-(1 : ℝ) / 16) →
    pr (PMF.uniformOfFintype (Line k × (Fin s → Bool) × (Fin s → Bool)))
        {ω | (f (Sum.inl ω.1)).eval (hybrid f i ω.2.1 ω.2.2) ≠ (f (Sum.inl ω.1)).eval ω.2.2 ∧
          onLine ω.1 (decodeOut enc (f.eval ω.2.1) i)}
      ≤ η * pr (PMF.uniformOfFintype (Line k × (Fin s → Bool) × (Fin s → Bool)))
        {ω | onLine ω.1 (decodeOut enc (f.eval ω.2.1) i)} := by sorry

end SamplingAC0
