-- Prove2me | Theorems.Thm_StretchDepth_critical_query_bound
-- name    : StretchDepth.critical_query_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:07:12.435441+00:00
-- url     : https://prove2.me/theorems/53bf5ec4-068d-488d-b8eb-ced66f5ddc6e
-- title:
--   Proof of Lemma 1 — the Critical Query bound
-- statement:
--   Let $N>n$, $q,d\ge1$, $1\le s<2^n/q$, $p=s/2^n$, $\ell=n-\log_2(qs)$, and let $H$ be a $(q,d)$-construction with no repeated queries. Fix an input $x$. For $1\le j\le d$ and naturals $t_{j-1},t_j$,
--   $$
--   \Pr_\rho\bigl[\exists G\supseteq\rho,\ t^G_{j-1}(\rho)=t_{j-1}\ \wedge\ t^G_j(\rho)=t_j\bigr]\le2^{Nt_{j-1}-\ell t_j}.
--   $$
--   Each critical query costs a factor $2^{-\ell}$, and each critical answer revealed in an earlier round pays back at most $2^{N}$.
--
--   Differences from the source:
--   - reading: Definition 1: without loss of generality no input is queried more than once → hypothesis NoRepeat H; reason: the proof on p.17 invokes it; no_repeat_normal_form removes it for Lemma 1, and the bound fails without it (q = 2, d = 1, n = 3, s = 1, a repeated query: Pr[t = 2] = 1/8 > 1/16)
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Lemma 1, p.16

import Definitions.Def_StretchDepth_IsConstruction
import Definitions.Def_StretchDepth_crit

namespace StretchDepth

/-- **Critical Query bound.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Lemma 1, p.16: "for any j ≤ d, tj−1, tj ∈ N, we have:
Prρ[∃G ⊇ ρ, tG j−1(ρ) = tj−1 ∧ tG j (ρ) = tj] ≤ 2^{Ntj−1−ℓtj}".

**Formalization Note.** `NoRepeat H` is the normal form of Definition 1, which the proof on p.17
invokes ("recall from Section 2 that we can assume no repeated queries are ever made"); without it
the bound fails. `1 ≤ j`, since the display names `t_{j−1}`. The exponent is real. -/
theorem critical_query_bound {n N m M : ℕ} (hN : n < N) (q d : ℕ) (hq : 1 ≤ q) (hd : 1 ≤ d) (s : ℝ)
    (hs : 1 ≤ s) (hqs : (q : ℝ) * s < 2 ^ n) (H : Bits m → RoundTree n N M)
    (hH : IsConstruction H q d) (hNR : NoRepeat H) (x : Bits m) (j t₀ t₁ : ℕ) (hj1 : 1 ≤ j)
    (hjd : j ≤ d) :
    probRho (s / 2 ^ n) (fun ρ : PartialAssign n N =>
        ∃ G, Extends G ρ ∧ crit ρ G (H x) (j - 1) = t₀ ∧ crit ρ G (H x) j = t₁) ≤
      (2 : ℝ) ^ ((N : ℝ) * t₀ - ell n q s * t₁) := by sorry

end StretchDepth
