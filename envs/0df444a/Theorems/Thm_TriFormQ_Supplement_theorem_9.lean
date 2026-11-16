-- Prove2me | Theorems.Thm_TriFormQ_Supplement_theorem_9
-- name    : TriFormQ.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:59:42.606907+00:00
-- url     : https://prove2.me/theorems/37b52924-364f-4338-99e0-051dc4f04091
-- title:
--   Theorem 9 — identify $f\in\mathcal T$ or reject $f\notin\mathcal T$ with $O_q(\log^{2/3}L\cdot\log\frac1\varepsilon)$ queries (corrected: $\max\{1,\log^{2/3}L\}\lambda(\varepsilon)$)
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $C=C(q)$ such that the following holds for every $n\ge 0$, every $L\ge1$, every explicit list $\mathcal T=(T^1,\dots,T^L)$ of trilinear forms on $\mathbb F_q^n\times\mathbb F_q^n\times\mathbb F_q^n$ (repetitions allowed) and every confidence parameter $\varepsilon\in(0,1)$. There is a randomized quantum query algorithm, depending only on $n$, $\mathcal T$ and $\varepsilon$, which is given oracle access $O_f:|x,y,z,b\rangle\mapsto|x,y,z,b+f(x,y,z)\rangle$ to a hidden trilinear form $f$ on $\mathbb F_q^n$, outputs either an index $j\in[L]$ or "reject", and satisfies, for **every** trilinear form $f$:
--
--   1. every run of positive probability makes at most
--   $$C\cdot\max\{1,(\log_2 L)^{2/3}\}\cdot\lambda(\varepsilon),\qquad \lambda(\varepsilon)=\max\{1,\log_2(1/\varepsilon)\},$$
--   queries;
--   2. if $f=T^i$ for some $i$, it outputs an index $j$ with $T^j=f$ with probability at least $1-\varepsilon$;
--   3. if $f\notin\mathcal T$, it outputs "reject" with probability at least $1-\varepsilon$.
--
--   This strengthens the main theorem (Theorem 1, the mission's goal) by a rejection guarantee: the same query budget suffices to certify that the hidden form is not in the list.
--
--   **Formalization Note** The algorithm is the base mission's `AdaptiveAlg` with output type `Option (Fin L)` (`none` = reject), chosen before $f$; query counts are `maxQueries` (worst case over runs of positive probability on the oracle actually queried) and probabilities are `outProb`. The constant $C$ is quantified after the field and before $n$, $L$, the list and $\varepsilon$, and does not depend on $n$.
--
--   Differences from the source:
--   - correction: $\log(1/\varepsilon)$ → $\lambda(\varepsilon)=\max\{1,\log_2(1/\varepsilon)\}$; reason: the printed factor tends to $0$ as $\varepsilon\to1$ (counterexample as for the goal: $q=2$, $L=2^k$ distinct forms, $\log_2(1/\varepsilon)=1/(2Ck^{2/3})$ allows fewer than one query, and a $0$-query algorithm identifies the hidden form with probability $\le 2^{-k}<1-\varepsilon$); for $\varepsilon\le1/2$ the two agree.
--   - correction: $\log^{2/3}L$ → $\max\{1,(\log_2L)^{2/3}\}$; reason: at $L=1$ the printed bound is $0$ queries, and a $0$-query algorithm has one output law independent of the oracle, so with $T^1=0$ on $\mathbb F_q^1$, $\varepsilon<1/2$, it cannot output $1$ with probability $\ge1-\varepsilon$ on $f=0$ and also reject with probability $\ge1-\varepsilon$ on $f=xyz\notin\mathcal T$; for $L\ge2$ the two agree.
--   - encoding: $O_q(\cdot)$ → one constant $C$ depending only on $\mathbb F_q$, quantified before $n$, $L$, the list and $\varepsilon$, with logarithms base 2; reason: the meaning of $O_q$ (p.10: logarithms base 2).
--   - encoding: "a randomized quantum algorithm … identifies $f$ / rejects" → an `AdaptiveAlg` with output in `Option (Fin L)`, success "outputs `some j` with $T^j=f$", rejection "outputs `none`", query count `maxQueries` on the oracle of every $f$; reason: the base mission's model of randomized quantum query algorithms; the list may repeat forms, so any index of $f$ counts.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 9, p.41 (PDF p.44)

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_lam

namespace TriFormQ.Supplement

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 9, p.41 (PDF p.44):
"Let T = {T¹, …, T^L} be an explicit list of L trilinear forms over 𝔽_q^n, and let
f : 𝔽_q^n × 𝔽_q^n × 𝔽_q^n → 𝔽_q be a hidden trilinear form accessible only via an evaluation
oracle. For any confidence parameter ε ∈ (0, 1), there exists a randomized quantum algorithm that
makes at most O_q(log^{2/3} L · log(1/ε)) quantum queries to f and satisfies the following:
• If f ∈ T, the algorithm identifies f with probability at least 1 − ε.
• If f ∉ T, the algorithm detects this and rejects with probability at least 1 − ε."

**Formalization Note.** For every finite field `F` (`q = |F|`) there is one constant `C`, chosen
before `n`, `L`, the list and `ε`; the bound does not depend on `n`. The algorithm is a
`TriFormQ.AdaptiveAlg` with the standard oracle of the hidden form, chosen from `n`, the explicit
list and `ε` before the hidden form `f`, which ranges over **all** trilinear forms on `𝔽ⁿ`. Its
output is `Option (Fin L)`: `some j` means "f is Tʲ", `none` means "reject (f ∉ T)". "Identifies f"
is outputting `some j` with `Tʲ = f` (the list may contain repetitions). The query bound
(`maxQueries`, worst case over runs of positive probability) holds on the oracle of every `f`.
Two corrections of the printed bound (see the item's differences): `log(1/ε)` becomes
`λ(ε) = max{1, log₂(1/ε)}` as in the goal, and `log^{2/3} L` becomes `max{1, (log₂ L)^{2/3}}`,
since at `L = 1` the printed bound allows no query, and with no query the rejection clause fails.
Logarithms are base 2 (p.10). `n = 0` is allowed (the source does not restrict `n`). -/
theorem theorem_9 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], ∃ C : ℝ, ∀ n L : ℕ, 0 < L →
      ∀ (T : Fin L → TriForm F n) (ε : ℝ), 0 < ε → ε < 1 →
        ∃ A : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F (Option (Fin L)),
          ∀ f : TriForm F n,
            (A.maxQueries (oracle f) : ℝ) ≤
                C * max 1 ((Real.logb 2 L) ^ ((2 : ℝ) / 3)) * lam ε ∧
            ((∃ i, T i = f) →
                1 - ε ≤ A.outProb (oracle f) (fun o => ∃ j, o = some j ∧ T j = f)) ∧
            ((∀ i, T i ≠ f) → 1 - ε ≤ A.outProb (oracle f) (fun o => o = none)) := by sorry

end TriFormQ.Supplement
