-- Prove2me | Theorems.Thm_StretchDepth_planted_distribution
-- name    : StretchDepth.planted_distribution
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:50.974672+00:00
-- url     : https://prove2.me/theorems/7d2245fd-a091-445e-93d6-b76f410d3e30
-- title:
--   Proof of Theorem 1 — observations 1 and 2 on the planted experiment
-- statement:
--   Let $p\in[0,1]$. Let $G$ be uniform, $S$ include each input independently with probability $p$, and $w\in\{0,1\}^n$, $z\in\{0,1\}^N$ be uniform, all independent, and let $G'=G[w\mapsto z]$. For every real function $F$ of a function, a set and a string:
--
--   1. $\mathbb E\,F(G,S,z)$ is the same as under independent $(G,S)$ and $z$;
--   2. $\mathbb E\,F(G',S,z)=\mathbb E\,F(G,S,G(w))$.
--
--   Taking $F$ to depend on $S$ only through $T_{G|_{\overline S}}$ gives the printed statements: $(G,T,z)$ has the law of $(G,T)\sim D$ with independent $z$, and $(G',T',z)$ has the law of $(G,T,G(w))$.
--
--   Differences from the source:
--   - encoding: rho = G|_{S̄} with S the free set (overline on the rendered p.13, p.20) → freeOn G S; reason: notation only, the same partial assignment
--   - generalization: equality of the laws of (G, T, z) and (G′, T′, z), with N > n and M > m in force → equality of expectations of every real F of (G, S, ·), with no condition on n, N; reason: T and T′ are functions of (G, S) and (G′, S), so this implies the printed form; equality of all expectations on a finite space is equality of laws
-- source:
--   Korten, Tight Depth Lower Bounds for Stretch Amplification, STOC 2027 submission (manuscript sha256 32d209e2…), proof of Theorem 1, p.20

import Definitions.Def_StretchDepth_PartialAssign

namespace StretchDepth

/-- **Proof of Theorem 1, observations 1 and 2.**
Korten, *Tight Depth Lower Bounds for Stretch Amplification*, STOC 2027 submission (manuscript
sha256 32d209e2…), proof of Theorem 1, p.20: "1. The distribution (G, T, z)(G,G′,T,T ′,w,z)∼D′ equals the
distribution (G, T, z)(G,T)∼D,z∼{0,1}N . 2. The distribution (G′, T ′, z)(G,G′,T,T ′,w,z)∼D′ equals
the distribution (G, T, G(w))(G,T)∼D,w∼{0,1}n."

**Formalization Note.** Stated as equality of expectations of every real function `F` of
`(G, S, ·)`. `T` and `T′` are functions of `(G, S)` and `(G′, S)`, so taking
`F G S z = f G (T_{G|_{S̄}}) z` gives the printed form. -/
theorem planted_distribution {n N : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (F : (Bits n → Bits N) → Finset (Bits n) → Bits N → ℝ) :
    avgPlanted p (fun G S _ z => F G S z) =
        (∑ z : Bits N, avgGS p fun G S => F G S z) / 2 ^ N ∧
      avgPlanted p (fun G S w z => F (Function.update G w z) S z) =
        (∑ w : Bits n, avgGS p fun G S => F G S (G w)) / 2 ^ n := by sorry

end StretchDepth
