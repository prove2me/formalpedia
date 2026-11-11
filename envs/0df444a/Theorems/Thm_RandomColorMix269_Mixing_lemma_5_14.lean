-- Prove2me | Theorems.Thm_RandomColorMix269_Mixing_lemma_5_14
-- name    : RandomColorMix269.Mixing.lemma_5_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:04:39.890064+00:00
-- url     : https://prove2.me/theorems/0396ad76-5964-406f-8790-7c761c634da9
-- title:
--   Lemma 5.14 — w.h.p. a uniform $r$-subset $T\subseteq U$ has all components of $G[S\cup T]$ of size $\le K\ln n$ except with probability $n^{-a-2}$
-- statement:
--   Let $\eta\in(0,1)$, $d>1$, and let $p$ and $J\mapsto K_J$ satisfy both conclusions of Lemma 5.10. Let $q\ge(1+\eta)d$, $b=q^{-(D+1)}$, $C_{SI}>0$, $\zeta=p/4$ and $a=(4C_{SI}/b^2+2)\ln(4/\zeta)+2$. Fix $J>2a+6$ and $K=K_J$. Then, with probability tending to $1$ over $G\sim G(n,d/n)$,
--   $$
--   \mathbb P_{T\sim\binom Ur}\Big(\max_{R\text{ component of }G[S\cup T]}|R|>K\ln n\ \Big|\ G\Big)\le n^{-a-2},
--   $$
--   where $T$ is a uniformly random subset of $U$ of size $r=\lfloor\zeta|U|\rfloor$.
--
--   The inner probability is conditional on the graph; random blocks with large components are rare enough to be absorbed in Proposition 5.15.
--
--   Differences from the source:
--   - encoding: vertex set [n] and colour set [q] → Fin n and Fin q; reason: relabelling only
--   - encoding: with probability at least 1 − o_n(1) over G ∼ G(n,d/n), for all sufficiently large n → the probability of the event under LPCommunity.SBMRecovery.erProb n (d/n) tends to 1; reason: the published law clamps d/n to [0,1], which differs from G(n,d/n) only for the finitely many n < d
--   - generalization: d sufficiently large, p and K_J the constants of Lemma 5.10, C_SI the constant of Corollary 1.5 → every d > 1, every (p, K) satisfying the two conclusions of Lemma 5.10, every C_SI > 0; reason: the proof uses only Lemma 5.10's conclusions and the size of U; it specializes to the source's constants
--   - encoding: P_{T∼(U choose r)}(· | G) → fraction of r-subsets T of U with a large component; reason: uniform law on r-subsets
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #269 (October 2026), PDF sha256 467638f1abc0f57df1bc0dcd9abfd308eb90ddbaf4947dac3eefa5f293ac6f05, p.34, Lemma 5.14

import Definitions.Def_RandomColorMix269_Mixing_Parameters

open scoped Classical BigOperators
set_option autoImplicit false

namespace RandomColorMix269.Mixing

/-- Lemma 5.14, p.34. K_J and p are those of Lemma 5.10; the inner
probability is conditional on the graph and uniform over r-subsets of U. -/
theorem lemma_5_14 (η d p : ℝ) (K : ℝ → ℝ) (hη : 0 < η) (hη1 : η < 1)
    (hd : 1 < d) (hPC : PercolationConstants η d p K) (q : ℕ)
    (hq : (1 + η) * d ≤ q) (Csi : ℝ) (hCsi : 0 < Csi)
    (J : ℝ) (hJ : 2 * exponentA Csi (marginalLower q (cutoff η d)) p + 6 < J) :
    WithHighProbability d (fun n G =>
      randomBlockFailure G (cutoff η d) p (K J) ≤
        (n : ℝ) ^ (-exponentA Csi (marginalLower q (cutoff η d)) p - 2)) := by sorry

end RandomColorMix269.Mixing
