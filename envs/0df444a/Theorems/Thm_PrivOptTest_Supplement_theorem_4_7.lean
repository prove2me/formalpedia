-- Prove2me | Theorems.Thm_PrivOptTest_Supplement_theorem_4_7
-- name    : PrivOptTest.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:36:29.613058+00:00
-- url     : https://prove2.me/theorems/a53a2d97-c2ec-4749-8bfd-8cd64f1e20a9
-- title:
--   Theorem 4.7, p.30 — Algorithm 3 is an $\varepsilon$-private halfspace tester once $t\gtrsim\frac{d^2\log(2m)}{\varepsilon}\big(d+\log\frac{d\log(2m)}{\beta}\big)$
-- statement:
--   For every container constant $c>0$ there is a constant $C>0$ such that the following holds. Let $d\ge1$, let $\mathcal X\subseteq\mathbb R^d$ be finite with $|\mathcal X|=m$, let $\mathcal W$ be a dual discretization of $\mathcal X$ (Lemma 4.3) and $\mathcal C$ a halfspace container map with constant $c$ at $\eta=1/4$ (Lemma 4.5). Let $\varepsilon\in(0,1]$, $\beta\in(0,1)$ and $t\in[n]$ with
--   $$t\ge C\,\frac{d^2\log(2m)}{\varepsilon}\Big(d+\log\frac{d\log(2m)}{\beta}\Big).$$
--   Then Algorithm 3, run with $\mathcal W$ and $\mathcal C$, is an $\varepsilon$-private tester for $\mathcal H_{\mathrm{hs}}$ with resolution $t$ and success probability at least $1-\beta$: it is $\varepsilon$-two-party differentially private on all inputs, outputs Far with probability at least $1-\beta$ when $\mathrm{opt}_{\mathcal H_{\mathrm{hs}}}(S_A,S_B)\ge t$, and Match with probability at least $1-\beta$ when $\mathrm{opt}_{\mathcal H_{\mathrm{hs}}}(S_A,S_B)=0$.
--
--   The resolution does not depend on the dataset size $n$; together with Theorem 4.1 it pins the domain-size dependence of halfspace testing at $\log m$, up to polynomial factors in $d$.
--
--   **Formalization Note** $\log$ is natural; it sits under $C$.
--
--   Differences from the source:
--   - reading: “Let c be a universal constant”, one letter for the threshold constant and Lemma 4.5’s container constant (line 3) → ∀ container constant c > 0, ∃ threshold constant C > 0; reason: the proof needs k ≥ 2α + 2 with α depending on the container constant, so the threshold constant is a separate universal constant determined by it; the Lean statement holds at Lemma 4.5’s c, whatever it is
--   - generalization: W_disc of Lemma 4.3 and C(·, 1/4) of Lemma 4.5 → any inputs W, cont satisfying IsDualDisc X W and IsContainerMap c cont (closed halfspaces only); reason: these are exactly the lemmas’ conclusions, so the objects of the lemmas qualify; requiring closed halfspaces only is weaker than Lemma 4.5’s every affine halfspace
--   - encoding: d (dimension of ℝ^d) → 1 ≤ d; reason: log(d log(2m)/β) is undefined at d = 0
--   - encoding: line 3 computes α → α not computed by the protocol; reason: no later line uses α; it appears only in the analysis
--   - encoding: C ∼ EM(q, R_r, S, ε₀) → inverse-CDF sample from one uniform coin per round; reason: the sample has the law of Lemma B.4 with Δ = 1
--   - encoding: log (base unstated) → Real.log; reason: any fixed base only rescales C
--   - encoding: testers on multisets → IsTester … over protocols on sequences Fin n → X; reason: Algorithm 3 reads its input only through the local errors f_A, f_B, which do not depend on the order of the records, and sequence neighbours are multiset neighbours
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 4.7, p.30; Algorithm 3, p.30; Lemmas 4.3 and 4.5, pp.28–29

import Mathlib
import Definitions.Def_PrivOptTest_IsTester
import Definitions.Def_PrivOptTest_Supplement_HhsOn
import Definitions.Def_PrivOptTest_Supplement_IsContainerMap
import Definitions.Def_PrivOptTest_Supplement_algo3

namespace PrivOptTest

namespace Supplement

/-- **Theorem 4.7** (arXiv:2611.03599, manuscript sha256 4ac94dcf…, p.30; Algorithm 3, p.30; Lemmas
4.3 and 4.5, pp.28–29). For every container constant `c > 0` there is `C > 0` such that the following
holds. Let `d ≥ 1`, let `X ⊆ ℝ^d` be finite with `|X| = m`, let `W` be a finite dual discretization of
`X` (the conclusion of Lemma 4.3) and `cont` a halfspace container map with constant `c` at `η = 1/4`
(the conclusion of Lemma 4.5). Let `ε ∈ (0, 1]`, `β ∈ (0, 1)`, `t ∈ [n]` and
`t ≥ C (d² log(2m)/ε)(d + log(d log(2m)/β))`. Then Algorithm 3, run with `W` and `cont`, is an
ε-private tester for `H_hs` with resolution `t` and success probability at least `1 − β`.

**Formalization Note.** "Let `c` be a universal constant" names both the constant of the threshold and
Lemma 4.5's container constant, which enters line 3 and `|C(S, 1/4)| ≤ 8^{cd}`. The statement takes the
container constant first and gives the threshold constant `C` after it, so it holds at the `c` of
Lemma 4.5 whatever that is. `W` and `cont` are inputs carrying exactly the conclusions of Lemmas 4.3
and 4.5. `log` is natural; it sits under `C`. `d ≥ 1` is needed for `log(d log(2m)/β)` to be defined. -/
theorem theorem_4_7 :
    ∀ c : ℝ, 0 < c → ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (X W : Finset (EuclideanSpace ℝ (Fin d))) (n t : ℕ) (ε β : ℝ)
        (cont : Finset (EuclideanSpace ℝ (Fin d)) → Finset (Finset (EuclideanSpace ℝ (Fin d)))),
        1 ≤ d → IsDualDisc X W → IsContainerMap c cont →
        0 < ε → ε ≤ 1 → 0 < β → β < 1 → 1 ≤ t → t ≤ n →
        C * ((d : ℝ) ^ 2 * Real.log (2 * X.card) / ε) *
            (d + Real.log (d * Real.log (2 * X.card) / β)) ≤ t →
        IsTester (algo3 X n t ε W cont) (HhsOn X) ε t β := by sorry

end Supplement

end PrivOptTest
