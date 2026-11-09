-- Prove2me | Theorems.Thm_TriFormQ_theorem_7
-- name    : TriFormQ.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:56:26.587907+00:00
-- url     : https://prove2.me/theorems/cb0c8459-ceca-433d-bd7c-672a745ce582
-- title:
--   Theorem 7 (pivot reduction): $f|_{Z_v\times S_V\times S_W}\equiv0$ with codimension $\le4\lceil\mathrm{AR}(f)+5\log_q2\rceil$ (corrected: $\max\{1,\log_2\rho\}$, $\lambda(\varepsilon)$)
-- statement:
--   Let $\mathbb F_q$ be a finite field. There is a constant $C$ (depending only on $q$) such that for every $n$, every $\rho$, every base point $v\in\mathbb F_q^n$ and every $\varepsilon>0$ there is a randomized quantum query algorithm, depending on $n,\rho,v,\varepsilon$ only, with the following property. For every trilinear form $f$ on $\mathbb F_q^n$ with $\mathrm{AR}(f)\le\rho$ for which $v$ is a good base point, with fiber $S_U=Z_v$, given the evaluation oracle of $f$, the algorithm
--
--   1. makes at most
--   $$C\big(\rho\,\ell^2+\rho\,\ell\,\lambda(\varepsilon)+\ell\,\lambda(\varepsilon)^2\big),\qquad \ell=\max\{1,\log_2\rho\},\ \lambda(\varepsilon)=\max\{1,\log_2(1/\varepsilon)\},$$
--   queries on every run, and
--   2. with probability at least $1-\varepsilon$ outputs subspaces $S_V,S_W\le\mathbb F_q^n$ (as lists of covectors spanning their annihilators) such that $f(u,y,z)=0$ for all $u\in Z_v$, $y\in S_V$, $z\in S_W$, and
--   $$\mathrm{codim}(S_V)=\mathrm{codim}(S_W)\ \le\ 4\lceil \mathrm{AR}(f)+5\log_q2\rceil .$$
--
--   Together with the good fiber this gives a product of three subspaces of codimension $O(\mathrm{AR}(f))$ on which $f$ vanishes, so $f$ is determined by $O(\mathrm{AR}(f))$ bilinear slices.
--
--   Differences from the source:
--   - correction: $O(\mathrm{AR}(f)\log^2\mathrm{AR}(f)+\mathrm{AR}(f)\log\mathrm{AR}(f)\log\frac1\varepsilon+\log\mathrm{AR}(f)\log^2\frac1\varepsilon)$ → $C(\rho\ell^2+\rho\ell\lambda(\varepsilon)+\ell\lambda(\varepsilon)^2)$ with $\ell=\max\{1,\log_2\rho\}$; reason: the printed bound is negative when $\mathrm{AR}(f)<1$ and $\varepsilon$ is small ($f=u_1v_1w_1$ over $\mathbb F_3$ has $\mathrm{AR}=\log_3(9/5)\approx0.535$), so no algorithm meets it
--   - generalization: the algorithm is run with the parameters $r_{\max},T_{\mathrm{iter}}$ computed from $\mathrm{AR}(f)$, and the query bound is in $\mathrm{AR}(f)$ → the algorithm receives an upper bound $\rho\ge\mathrm{AR}(f)$, works for every $f$ with $\mathrm{AR}(f)\le\rho$, and the query bound is in $\rho$; the codimension bound keeps $\mathrm{AR}(f)$; reason: an oracle algorithm cannot see $\mathrm{AR}(f)$; with $\rho=\mathrm{AR}(f)$ this is the printed statement
--   - reading: successfully find $S_V\le V$ and $S_W\le W$ with codimension at most … → success also requires $f(u,y,z)=0$ for $u\in Z_v$, $y\in S_V$, $z\in S_W$; reason: Fig. 7's caption ("so that $f[u]|_{S_V\times S_W}\equiv0$ for every $u\in Z_v$", p.34) and the §6 overview (p.29); without it $S_V=S_W=\mathbb F_q^n$ would do
--   - encoding: $S_U=Z_e\le U$; output $S_V,S_W$ → $S_U$ is the fiber $Z_v$; $S_V,S_W$ are output as lists spanning $S_V^\perp,S_W^\perp$ (Fig. 7, step (11)), codimension $n-\dim$; reason: "$Z_e$" is a typo for $Z_v$; the annihilator lists determine the subspaces
--   - encoding: randomized quantum query algorithm making at most $X$ queries → an `AdaptiveAlg` (rounds of the platform's `QueryAlg` against the standard oracle, full measurement, classical choice of the next round) chosen before the oracle, whose worst-case query count over positive-probability runs on that oracle is at most $X$; reason: platform query model; classical coins are 0-query rounds and offline computation on explicit data is free, as in the paper
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 7, p.34 (PDF p.37), with Fig. 7 and its caption, p.34 (PDF p.37)

import Definitions.Def_TriFormQ_oracle
import Definitions.Def_TriFormQ_AdaptiveAlg_outProb
import Definitions.Def_TriFormQ_AdaptiveAlg_maxQueries
import Definitions.Def_TriFormQ_lam
import Definitions.Def_TriFormQ_goodSet
import Definitions.Def_TriFormQ_fiber
import Definitions.Def_TriFormQ_constraintSub

namespace TriFormQ

open Classical in
/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 7, p.34 (PDF p.37), with
Fig. 7's caption ("Algorithm for identifying subspaces S_V and S_W so that f[u]|_{S_V×S_W} ≡ 0
for every u ∈ Z_v", p.34): "Given a good base point v ∈ G as defined in Definition 2. Denote the
good fiber of Z over v by S_U, i.e. S_U = Z_v ≤ U. Then there is a randomized algorithm which, for
any ε > 0, successfully find S_V ≤ V and S_W ≤ W with codimension at most
codim_V(S_V) = codim_W(S_W) ≤ 4⌈AR(f) + 5 log_q 2⌉ with probability at least 1 − ε and use at most
O(AR(f) log²(AR(f)) + AR(f) log(AR(f)) log(1/ε) + log(AR(f)) log²(1/ε)) quantum queries."

**Formalization Note.** The algorithm is given `n`, an upper bound `ρ ≥ AR(f)`, the base point
`v` and `ε` (not `AR(f)` itself, and not the fiber `Z_v`), and is chosen before the oracle. It
outputs `S_V`, `S_W` as lists of covectors spanning `S_V^⊥`, `S_W^⊥` (Fig. 7, step (11));
`constraintSub` is the subspace they cut out and `codim = n − finrank`. The success event has
three parts: `f(u, y, z) = 0` for `u ∈ Z_v`, `y ∈ S_V`, `z ∈ S_W`; equal codimensions; and the
codimension bound in the actual `AR(f)`. The query bound uses `ℓ = max{1, log₂ ρ}` and
`λ(ε) = max{1, log₂(1/ε)}` in place of `log AR(f)` and `log(1/ε)` (see the item's
differences). -/
theorem theorem_7 {F : Type} [Field F] [Fintype F] [DecidableEq F] :
    ∃ C : ℝ, ∀ (n : ℕ) (ρ ε : ℝ) (v : Vec F n), 0 < ε →
      ∃ A : AdaptiveAlg (Vec F n × Vec F n × Vec F n) F (List (Vec F n) × List (Vec F n)),
        ∀ θ : TriForm F n, AR θ ≤ ρ → v ∈ goodSet θ →
          (A.maxQueries (oracle θ) : ℝ) ≤
              C * (ρ * (max 1 (Real.logb 2 ρ)) ^ 2 + ρ * max 1 (Real.logb 2 ρ) * lam ε +
                max 1 (Real.logb 2 ρ) * lam ε ^ 2) ∧
          1 - ε ≤ A.outProb (oracle θ) (fun c =>
            (∀ u ∈ fiber θ v, ∀ y ∈ constraintSub c.1, ∀ z ∈ constraintSub c.2,
                TriForm.eval θ u y z = 0) ∧
            Module.finrank F (constraintSub c.1) = Module.finrank F (constraintSub c.2) ∧
            n - Module.finrank F (constraintSub c.1) ≤
              4 * ⌈AR θ + 5 * Real.logb (Fintype.card F) 2⌉₊) := by sorry

end TriFormQ
