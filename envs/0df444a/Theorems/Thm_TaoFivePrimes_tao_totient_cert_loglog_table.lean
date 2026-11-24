-- Prove2me | Theorems.Thm_TaoFivePrimes_tao_totient_cert_loglog_table
-- name    : TaoFivePrimes.tao_totient_cert_loglog_table
-- status  : Proved
-- author  : @andreaskapfer
-- created : 2026-09-17T20:49:43.152205+00:00
-- url     : https://prove2.me/theorems/b058b30c-7dad-4676-befc-7195b69755dd
-- title:
--   Certified log-log table for the primorials
-- statement:
--   Let $p_{k+1}$ be the $(k+1)$-st prime and let
--   $$ P_{k+1} \;=\; \mathrm{primorial}(p_{k+1}) \;=\; \prod_{p \le p_{k+1}} p \;=\; p_1 p_2 \cdots p_{k+1} $$
--   be the primorial, so that $\log\log P_{k+1} = \log \vartheta(p_{k+1})$ in terms of Chebyshev's function $\vartheta$. The table `rll m` records certified rational lower bounds for $\log \vartheta(p_m) = \log\log P_m$, obtained from the integer logarithm table `clbZ` (four-decimal lower bounds for $\log p$) by adding the entries for the primes up to $p_{m-1}$.
--
--   The theorem states that the table is certified against Mathlib's primorial: for every $3 \le k \le 64$,
--   $$ \mathrm{rll}(k+1) \;\le\; \log\log\bigl(\mathrm{primorial}(p_{k+1})\bigr). $$
--
--   This is the link between the numerical tables and the real-logarithm inequality of the finite verification: if $n \ge P_m$ is an integer and $m$ is the least index with $n < \mathrm{primorial}(p_m)$, then $\log\log n \ge \log\log P_m \ge \mathrm{rll}(m)$, and since $t \mapsto e^{\gamma} t + 2.50637/t$ is increasing for $t \ge 1.19$, the certified table inequality $Q_m < \mathrm{rll}(m)\,e^{\gamma}_{\mathrm{lo}} + 2.50637/\mathrm{rll}(m)$ dominates the right-hand side of the Rosser--Schoenfeld bound at $n$.
--
--   *Formalization note.* The range $3 \le k \le 64$ corresponds to $4 \le k+1 \le 65$, the range of the table `rll`; the proof is a finite sequence of exponential certificates, one for each table entry.
-- source:
--   Numerical certificate for the finite part of the Rosser--Schoenfeld totient bound: J. B. Rosser and L. Schoenfeld, *Approximate formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64--94, Section 3 and Theorem 15; the tables are certified in this development using the exponential certificates of `Def_TaoFivePrimes_totient_cert_tables`.

import Definitions.Def_TaoFivePrimes_totient_cert_tables
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace TaoFivePrimes

theorem tao_totient_cert_loglog_table (k : ℕ) (hk : k ∈ Finset.Icc 3 64) :
    (rll (k+1) : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime k) : ℝ)) := by sorry

end TaoFivePrimes
