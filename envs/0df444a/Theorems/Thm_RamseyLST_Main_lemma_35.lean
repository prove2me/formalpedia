-- Prove2me | Theorems.Thm_RamseyLST_Main_lemma_35
-- name    : RamseyLST.Main.lemma_35
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T17:08:02.646419+00:00
-- url     : https://prove2.me/theorems/d0712e0d-4d98-4d56-8ae5-5fd44df0d5ae
-- title:
--   Lemma 35 — the Case 2 ratio bound: some $i \in [t]$ has $w(Q_{i-1})^{\psi_2} \ge w(Q_i)\,w(Z^{in})^{\psi_2-1}$
-- statement:
--   Let $q>1$ and let $t\ge1$ be an integer, and put $\psi_2=(\log q)^{-1/t}$ (base 2). Let $Z^{in}$ be a finite candidate core with a nonnegative weight function $w$ and $w(Z^{in})>0$, where $w(Q)=\sum_{z\in Q\cap Z^{in}}w(z)$. Let $Q_0,\dots,Q_t$ be sets with
--
--   $$w(Q_0)\ge\frac{w(Z^{in})}{q}\qquad\text{and}\qquad w(Q_t)\le\frac{w(Z^{in})}{2}.$$
--
--   Then there is an $i\in\{1,\dots,t\}$ with
--
--   $$w(Q_{i-1})^{\psi_2}\ \ge\ w(Q_i)\,w(Z^{in})^{\psi_2-1}.$$
--
--   This is the bound for Case 2 of CreatePetal (a heavy candidate core point near the petal), in which the weights of the candidate petals grow by a factor of at most $q$.
--
--   Differences from the source:
--   - generalization: q = 2^t and t ≥ t_0 ≥ 8, the parameters of §6 (Lemma 46, p. 56; proof of Theorem 25) → every real q > 1 and every integer t ≥ 1; reason: the proof uses only ψ_2 > 0 and q^{ψ_2^t} = 2, which hold for every q > 1 and t ≥ 1; it specializes to q = 2^t
--   - generalization: the nested petals Q_0 ⊆ Q_1 ⊆ … ⊆ Q_t of CreatePetal → arbitrary sets Q_0, …, Q_t; reason: the proof does not use the nesting
--   - generalization: positive weights w : Z^in → ℝ>0 with Z^in non-empty → nonnegative weights on Z^in with w(Z^in) > 0; reason: positive weights on a non-empty core are a special case; w(Z^in) > 0 keeps the power w(Z^in)^{ψ_2−1} defined
--   - reading: sets Q_0, …, Q_t and i ∈ [t] → t a natural number, sets Q 0, …, Q t (a function ℕ → Finset whose values beyond t are unused), i ∈ {1, …, t}; reason: the indexing requires an integer t, and the proof iterates over i = 1, …, t
-- source:
--   Bartal, Hovav, Nearly Tight Low-Stretch Ramsey Spanning Trees, STOC 2027 submission (manuscript sha256 bcaed0afb9db0cccb453599c9f6915e958922563d3989766c4affc99a15de44d), p. 48 (PDF 52), Lemma 35

import Mathlib
import Definitions.Def_RamseyLST_Main_Weights

namespace RamseyLST.Main

/-- Lemma 35 (p. 48): let `q > 1`, `t ≥ 1`, let `w ≥ 0` be a weight function on the candidate
core `Zin` with `w(Zin) > 0`, and let `Q₀, …, Q_t` be sets with `w(Q₀) ≥ w(Zin)/q` and
`w(Q_t) ≤ w(Zin)/2`. Then some `i ∈ {1, …, t}` satisfies
`w(Q_{i−1})^{ψ₂} ≥ w(Q_i) · w(Zin)^{ψ₂−1}`, where `ψ₂ = (log₂ q)^{−1/t}`. -/
theorem lemma_35 (q : ℝ) (hq : 1 < q) (t : ℕ) (ht : 1 ≤ t)
    (ι : Type) [DecidableEq ι] (Zin : Finset ι) (w : ι → ℝ) (hw : ∀ z ∈ Zin, 0 ≤ w z)
    (hpos : 0 < setWeight Zin w Zin) (Q : ℕ → Finset ι)
    (hQ0 : setWeight Zin w Zin / q ≤ setWeight Zin w (Q 0))
    (hQt : setWeight Zin w (Q t) ≤ setWeight Zin w Zin / 2) :
    ∃ i ∈ Finset.Icc 1 t,
      setWeight Zin w (Q i) * setWeight Zin w Zin ^ (psi2 q t - 1) ≤
        setWeight Zin w (Q (i - 1)) ^ psi2 q t := by sorry

end RamseyLST.Main
