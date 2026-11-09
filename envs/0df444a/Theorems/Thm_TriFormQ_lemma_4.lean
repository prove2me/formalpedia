-- Prove2me | Theorems.Thm_TriFormQ_lemma_4
-- name    : TriFormQ.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:49:08.065207+00:00
-- url     : https://prove2.me/theorems/4d5bc0fa-1e37-4ce2-a508-f3cc8b6cc1de
-- title:
--   Lemma 4 (verification tests): one-sided equality test with $O_q(\lambda(\varepsilon))$ queries for matrices and trilinear forms (corrected: $\max\{1,\log_2(1/\varepsilon)\}$)
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $C$ (depending only on $q$) with the following two properties.
--
--   1. For every $n$, every explicitly given $M'\in M_n(\mathbb F_q)$ and every $\varepsilon>0$ there is a randomized quantum query algorithm, with access to the evaluation oracle of an unknown bilinear form $x^\top My$, that makes at most $C\,\lambda(\varepsilon)$ queries on every oracle, where $\lambda(\varepsilon)=\max\{1,\log_2(1/\varepsilon)\}$, and that accepts with probability exactly $1$ if $M=M'$ and with probability at most $\varepsilon$ if $M\ne M'$.
--   2. The same holds for trilinear forms: for every explicitly given $T'$ on $\mathbb F_q^n$ and $\varepsilon>0$ there is such a one-sided tester with the evaluation oracle of an unknown trilinear form $T$, accepting surely if $T=T'$ and with probability at most $\varepsilon$ if $T\ne T'$.
--
--   These tests let the algorithm confirm a candidate cheaply; they are used to check learned slices and candidate base points.
--
--   Differences from the source:
--   - correction: at most $O_q(\log_q(1/\varepsilon))$ quantum queries → at most $C\cdot\max\{1,\log_2(1/\varepsilon)\}$ queries; reason: as $\varepsilon\to1$ the printed bound is below one query; a 0-query tester has the same acceptance probability on $M=M'$ and on $M\ne M'$, so it is $1>\varepsilon$ on $M\ne M'$; identical for $\varepsilon\le 1/2$ up to the constant
--   - encoding: an oracle matrix $M$ with query access → the evaluation oracle of the bilinear form $x^\top My$; reason: the paper's quantum queries to a matrix are evaluation queries (Corollary 4)
--   - encoding: $O_q$ in each of the two claims → one constant $C$ for both clauses, chosen before $n$, the explicit input and $\varepsilon$; reason: "the same query bound" for trilinear forms
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 4 (Verification tests), p.15 (PDF p.18)

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_bilOracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_lam

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Lemma 4 (Verification tests),
p.15 (PDF p.18): "There is a one-sided randomized algorithm A, which on inputs of an explicitly
given matrix M′, an oracle matrix M with query access and ε > 0, makes at most O_q(log_q(1/ε))
quantum queries to the oracle such that: if M′ = M, then Pr[A accepts] = 1; if M′ ≠ M,
Pr[A accepts] ≤ ε. The same query bound and algorithm behavior hold for trilinear forms as
well."

**Formalization Note.** One constant `C` (depending only on the field) serves both clauses. The
oracle is the evaluation oracle of the bilinear form `xᵀMy` (resp. the trilinear form);
"accepts" is output `true`. The tester is chosen from `n`, `M′` (resp. `θ′`) and `ε`, before the
oracle. Correction: the bound `O_q(log_q(1/ε))` is `C · max{1, log₂(1/ε)}` (see the item's
differences). -/
theorem lemma_4 {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ,
      (∀ (n : ℕ) (M' : Matrix (Fin n) (Fin n) F) (ε : ℝ), 0 < ε →
        ∃ A : AdaptiveAlg (Vec F n × Vec F n) F Bool, ∀ M : Matrix (Fin n) (Fin n) F,
          (A.maxQueries (bilOracle M) : ℝ) ≤ C * lam ε ∧
          (M = M' → A.outProb (bilOracle M) (fun b => b = true) = 1) ∧
          (M ≠ M' → A.outProb (bilOracle M) (fun b => b = true) ≤ ε)) ∧
      (∀ (n : ℕ) (θ' : TriForm F n) (ε : ℝ), 0 < ε →
        ∃ A : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F Bool, ∀ θ : TriForm F n,
          (A.maxQueries (oracle θ) : ℝ) ≤ C * lam ε ∧
          (θ = θ' → A.outProb (oracle θ) (fun b => b = true) = 1) ∧
          (θ ≠ θ' → A.outProb (oracle θ) (fun b => b = true) ≤ ε)) := by sorry

end TriFormQ
