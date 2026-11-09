-- Prove2me | Theorems.Thm_ParityBarrier563_Trilinear_lemma_5_5
-- name    : ParityBarrier563.Trilinear.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:10:19.385202+00:00
-- url     : https://prove2.me/theorems/1a58fb64-b70f-4593-934a-25681adb7ce7
-- title:
--   Lemma 5.5 — some seed a has E_φ corr_k(g^a_φ) ≤ 2^{−Ω(m)} for a q-random restriction φ
-- statement:
--   Let $k\ge b\ge1$ be integers, $0<q\le1$, $p=b/(64k)$ and $m=qpn$ (a real number). Suppose that $m\le n^{3/5}$ and that $m$ is at least a sufficiently large absolute threshold $M\ge2$. Suppose also that for every set $V$ of at most $4m$ variables, every $b$-CNF on $\{0,1\}^V$ is a sum of at most $2^{|V|/128}$ functions $\mathrm{cl}_b(S)$ with $|S|\le m^{1/8}$. Then there is a seed $a\in\{0,1\}^{2n-1}$ such that the sign $g^a$ of the slice $f^a_n$ satisfies
--
--   $$\mathbb E_\varphi\,\mathrm{corr}_k\bigl(g^a_\varphi\bigr)\le2^{-c\,m},$$
--
--   where $\varphi$ is a $q$-random restriction of the $2n$ variables $x,y$ and $c>0$ is an absolute constant.
--
--   This is the hardness of a random slice after the depth-reduction restriction; it feeds Lemma 5.1 in the proof of Theorem 1.1.
--
--   Differences from the source:
--   - encoding: m sufficiently large; 2^{−Ω(m)} → ∃ c > 0 and a threshold M ≥ 2, both chosen before n, k, b and q, with M ≤ m and bound 2^{−c·m}; reason: the meaning of 'sufficiently large' and Ω with absolute constants
--   - encoding: every set V of at most 4m variables → every finite type V (in Lean's base universe) with |V| ≤ 4m; reason: variable sets are finite types; the hypothesis is only used for subsets of the 2n data variables
-- source:
--   Nikolai Chukhin, Xin Li, Ivan Mihajlin, Yan Zhong, Breaking the Parity Barrier for Constant-Depth Circuits, STOC 2027 submission #563 (October 2026), SHA-256 e50e7ff9480ef7c23095e91345faf20f73773bc111e3b0eed2da71a28f7f9462, Lemma 5.5, printed p.18 (PDF p.20)

import Mathlib
import Definitions.Def_ParityBarrier563_Trilinear_Correlation
import Definitions.Def_ParityBarrier563_Trilinear_TrilinearFunction

set_option autoImplicit false

namespace ParityBarrier563.Trilinear

/-- Lemma 5.5, printed p.18 / PDF 20. `m = qpn` with `p = b/(64k)`; `φ` is a `q`-random
restriction of the `2n` data variables `x, y`. -/
theorem lemma_5_5 :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℝ, 2 ≤ M ∧ ∀ (n k b : ℕ) (q m : ℝ),
      1 ≤ b → b ≤ k → 0 < q → q ≤ 1 → m = q * ((b : ℝ) / (64 * k)) * n →
      M ≤ m → m ≤ (n : ℝ) ^ ((3 : ℝ) / 5) →
      (∀ (V : Type) [Fintype V] [DecidableEq V], (Fintype.card V : ℝ) ≤ 4 * m →
        HasClosureDecomp b V ((2 : ℝ) ^ ((Fintype.card V : ℝ) / 128)) (m ^ ((1 : ℝ) / 8))) →
      ∃ a : Fin (2 * n - 1) → Bool,
        restrExpect q (fun φ : Restriction (SliceVar n) =>
          corr k (restrict φ (sgn (slice n a)))) ≤ (2 : ℝ) ^ (-(c * m)) := by sorry

end ParityBarrier563.Trilinear
