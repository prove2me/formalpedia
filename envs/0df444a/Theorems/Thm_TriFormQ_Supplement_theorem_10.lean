-- Prove2me | Theorems.Thm_TriFormQ_Supplement_theorem_10
-- name    : TriFormQ.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:00:30.809048+00:00
-- url     : https://prove2.me/theorems/856602e1-6086-4805-b0c9-df67c4d4eeb0
-- title:
--   Theorem 10 — a $T$-query algorithm for Linear Isomorphism-$\mathrm{IP}_q$ yields a $T$-query algorithm for the Linear Simon's problem
-- statement:
--   Let $\mathbb F_q$ be a finite field and $n\ge0$. For a hidden matrix $A\in\mathbb F_q^{n\times n}$ with the promise $\mathrm{rk}(A)\in\{n,n-1\}$, the **Linear Simon's problem** gives oracle access to $O_{LS}:|x\rangle|z\rangle\mapsto|x\rangle|z+Ax\rangle$, and the **Linear Isomorphism-$\mathrm{IP}_q$ problem** gives oracle access to $O_{LI}:|x\rangle|y\rangle|b\rangle\mapsto|x\rangle|y\rangle|b+\mathrm{IP}_q(Ax,y)\rangle$, where $\mathrm{IP}_q(u,v)=\sum_iu_iv_i$; both ask whether $\mathrm{rk}(A)=n$.
--
--   For every query budget $T\in\mathbb N$ and every success level $p$: if there is a randomized quantum query algorithm $B$ for the Linear Isomorphism-$\mathrm{IP}_q$ problem that, for every promised $A$, makes at most $T$ queries to $O_{LI}$ on every run of positive probability and answers correctly with probability at least $p$, then there is a randomized quantum query algorithm $B'$ for the Linear Simon's problem that, for every promised $A$, makes at most $T$ queries to $O_{LS}$ on every run of positive probability and answers correctly with probability at least $p$.
--
--   Combined with the $\Omega(n)$ quantum query lower bound for the Linear Simon's problem (van Apeldoorn–Gribling), this gives the paper's Corollary 8: deciding linear isomorphism of the bilinear form $\mathrm{IP}_q(Ax,y)$ needs $\Omega(n)$ queries.
--
--   **Formalization Note** Algorithms are the base mission's `AdaptiveAlg` with Boolean output (`true` means $\mathrm{rk}(A)=n$); the $O_{LS}$ answers lie in the additive group $\mathbb F_q^n$. Nothing is required of $B$ off the promise. $n-1$ is natural-number subtraction; at $n=0$ the promise is $\mathrm{rk}(A)=0=n$, as in the source.
--
--   Differences from the source:
--   - reading: "Linear Isomorphism-$\mathrm{IP}_p$" → Linear Isomorphism-$\mathrm{IP}_q$; reason: typo, Definition 4 and the proof use $\mathrm{IP}_q$.
--   - reading: "a $T$-query quantum algorithm for the problem" (no success level stated) → worst-case query count $\le T$ and success probability $\ge p$ on every promised $A$, for every $p\in\mathbb R$, with the same $T$ and $p$ for the new algorithm; reason: the paper fixes no success level; quantifying over all $p$ is the strongest reading and contains every fixed level such as $2/3$.
--   - encoding: oracles $O_{LS}$, $O_{LI}$ → `QAlgorithms.xorOracle` of $x\mapsto Ax$ (answers in $\mathbb F_q^n$) and of $(x,y)\mapsto\mathrm{IP}_q(Ax,y)$ (answers in $\mathbb F_q$), algorithms as `AdaptiveAlg` with Boolean output; reason: the base mission's model; same oracles.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 10, p.42 (PDF p.45); Definitions 3–4, p.41 (PDF p.44)

import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_Supplement_linSimonOracle
import Definitions.Def_TriFormQ_Supplement_linIsoIPOracle

namespace TriFormQ.Supplement

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 10, p.42 (PDF p.45):
"Suppose we have a T-query quantum algorithm for the Linear Isomorphism-IP_p problem. Then there is
a T-query quantum algorithm for the Linear Simon's problem." The problems are Definitions 3 and 4,
p.41 (PDF p.44): a hidden `A ∈ 𝔽_q^{n×n}` with the promise `rk(A) = n` or `rk(A) = n − 1`; decide
which holds.

**Formalization Note.** "IP_p" is read as `IP_q` (Definition 4 and the proof say `IP_q`). A
"T-query quantum algorithm for the problem" with success level `p` is a `TriFormQ.AdaptiveAlg`
with Boolean output (`true` = "rk A = n") whose worst-case query count (`maxQueries`) is at most
`T` and whose probability of the correct answer is at least `p` on the oracle of **every** promised
`A`; nothing is required off the promise. The paper fixes no success level, so the statement is
for every `p ∈ ℝ` and every `T ∈ ℕ`, and the new algorithm keeps both. The Linear Simon oracle
`O_LS` has answers in the additive group `𝔽_q^n` (`linSimonOracle`), the Linear Isomorphism-IP_q
oracle `O_LI` answers in `𝔽_q` (`linIsoIPOracle`). `n − 1` is natural-number subtraction: at
`n = 0` the promise is `rk A = 0 = n`, as in the source, where `rk A = −1` is impossible. -/
theorem theorem_10 :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n T : ℕ) (p : ℝ),
      (∃ B : AdaptiveAlg (Vec F n × Vec F n) F Bool,
          ∀ A : Matrix (Fin n) (Fin n) F, (A.rank = n ∨ A.rank = n - 1) →
            B.maxQueries (linIsoIPOracle A) ≤ T ∧
            p ≤ B.outProb (linIsoIPOracle A) (fun b => b = decide (A.rank = n))) →
      ∃ B' : AdaptiveAlg (Vec F n) (Vec F n) Bool,
        ∀ A : Matrix (Fin n) (Fin n) F, (A.rank = n ∨ A.rank = n - 1) →
          B'.maxQueries (linSimonOracle A) ≤ T ∧
          p ≤ B'.outProb (linSimonOracle A) (fun b => b = decide (A.rank = n)) := by sorry

end TriFormQ.Supplement
