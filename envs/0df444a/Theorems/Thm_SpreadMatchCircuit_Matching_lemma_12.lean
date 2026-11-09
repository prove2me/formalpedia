-- Prove2me | Theorems.Thm_SpreadMatchCircuit_Matching_lemma_12
-- name    : SpreadMatchCircuit.Matching.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:14.031223+00:00
-- url     : https://prove2.me/theorems/f47479d1-3140-4519-b76f-76b90dc80306
-- title:
--   Lemma 12 — Algorithm 1 has few new negative errors: $p(X_0\in N^0_g)\le 4^t\varepsilon$
-- statement:
--   There is an absolute constant $\alpha>0$ such that the following holds. Let $n=2N$ and $b<k\le N$ with $k\ge 1$. Let $X_1$ be a uniformly random matching with $k$ edges across the sides $[n/2]$ and $[n]\setminus[n/2]$, and let $X_0$ be $G(W_0)$ for $W_0\subseteq[n]$ uniformly random of size $b$. Let $t,\varepsilon,r$ be real numbers with $t\le b/100$, $0<\varepsilon$, and
--
--   $$r\ge\alpha\,\big(2t+\log^2(1/\varepsilon)\big)\Big(\frac{3n}{b}\Big)^2.$$
--
--   Let $g=h_1\wedge h_2$ be an AND gate whose predecessors have families $M_{h_1},M_{h_2}$ of sets of at most $t$ edges, and let $M_g$ be the output of Algorithm 1 run with $r,t$. Then the new negative errors for $M_g$ satisfy
--
--   $$p\big(X_0\in N^0_g\big)\le 4^t\cdot\varepsilon.$$
--
--   Together with Lemma 11 this bounds the error added at each gate by the approximation.
--
--   **Formalization Note** $4^t$ is a real power. The constant $\alpha$ is existential and precedes all other parameters; the source's $\alpha$ is that of Lemma 5, used here through Eq. (7).
--
--   For $t<1$, both predecessor families contain only empty terms (or are empty), and the new negative error set is empty. For $t\ge1$ and $\varepsilon\ge1/2$, the bound follows from probability being at most one. Thus no extra lower threshold on $t$ or upper threshold on $\varepsilon$ is needed.
--
--   Differences from the source:
--   - generalization: t, ε, r fixed by Eq. (7) from q, k, n, η, α with equality for r → any real t, ε with t ≤ b/100 and 0 < ε, and any r at least α(2t + log²(1/ε))(3n/b)²; reason: the parameters of Eq. (7) satisfy these conditions; t < 1 has no new negative errors, and for t ≥ 1, ε ≥ 1/2 the bound is trivial.
--   - generalization: h₁, h₂ gates of a monotone circuit with families computed by the approximation → arbitrary Boolean functions with arbitrary families of sets of at most t edges; reason: the gates of the source are an instance.
--   - generalization: lexicographic order and any largest m → an arbitrary linear order, which also breaks ties among largest m; reason: the source's choices are instances.
--   - encoding: α from Lemma 5 → an existential absolute α before all instance parameters; reason: the source supplies no numeral; a common constant for Lemmas 5 and 12 may be chosen by enlarging their constants, since larger r imposes stronger spreadness.
--   - encoding: the cover budget is named q → the cover budget is named b, and X₀ is the full incident graph G(W₀); reason: renaming keeps this local parameter independent of the goal promise threshold; the graph and its sampling law are unchanged.
--   - encoding: n even with sides [n/2] and its complement → vertices Fin (2N), sides of values below N and at least N; reason: the source's local construction needs n even, and the same instances result.
-- source:
--   Anup Rao, STOC 2027 submission #299 (October 2026), p. 12, Lemma 12 (proof pp. 12–13; Eq. (7), p. 11; Algorithm 1, p. 12)

import Mathlib
import Definitions.Def_SpreadMatchCircuit_Matching_Approximator

namespace SpreadMatchCircuit.Matching

/-- Lemma 12, p. 12: `p(X₀ ∈ N⁰_g) ≤ 4^t ε` for `M_g` the output of Algorithm 1, where `α` is the
absolute constant governing `r` in Eq. (7). -/
theorem lemma_12 :
    ∃ α : ℝ, 0 < α ∧
      ∀ (N k b : ℕ) (t ε r : ℝ), 1 ≤ k → k ≤ N → b < k →
        t ≤ (b : ℝ) / 100 → 0 < ε →
        α * (2 * t + Real.log (1 / ε) ^ 2) * (3 * (2 * (N : ℝ)) / (b : ℝ)) ^ 2 ≤ r →
        ∀ (ord : LinearOrder (Finset (Edge (2 * N)))) (G : AndGate N), G.SizeBounded t →
          uniformProb (Finset.powersetCard b (Finset.univ : Finset (Fin (2 * N))))
            (fun W => incident W ∈ G.newNeg b (G.algorithm1 ord k r t))
            ≤ (4 : ℝ) ^ t * ε := by sorry

end SpreadMatchCircuit.Matching
