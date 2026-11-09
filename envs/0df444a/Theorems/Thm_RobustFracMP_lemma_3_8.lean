-- Prove2me | Theorems.Thm_RobustFracMP_lemma_3_8
-- name    : RobustFracMP.lemma_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:59:07.922634+00:00
-- url     : https://prove2.me/theorems/7f266303-e9a5-4300-8677-da66db59c962
-- title:
--   Lemma 3.8 — additive smoothness of $r^{(\beta)}$
-- statement:
--   Throughout, $z\ge 1$ is an integer, $(P,\mathrm{dist})$ is a finite nonempty metric space (the dataset, with candidate centers $F=P$), $\lambda>0$ is the opening cost, and $r^{(\beta)}_p$ is the radius of Algorithm 1 computed on the true metric $\mathrm{dist}$; $[a]_+=\max\{a,0\}$.
--
--   For every scale factor $\beta>0$ and all $p,q\in P$, writing $r_q=r^{(\beta)}_q$, $B=B^{(\beta)}_q(r_q/2)$ and $R=R^{(\beta)}_q(r_q/2)$,
--
--   $$r^{(\beta)}_p\le r_q+2^{z-1}\beta\,\mathrm{dist}^z(p,q)+\frac1{|B|}\Bigl(\sum_{t\in B}(2^{z-1}-1)\,\beta\,\mathrm{dist}^z(t,q)+\sum_{t\in R}\bigl(r_q-\beta\,\mathrm{dist}^z(t,q)\bigr)\Bigr).$$
--
--   The ball $B$ contains $q$, so $|B|\ge1$. Unlike Lemma 3.7, the radii differ only by an additive term; this bound drives Claim 3.18 for the close pairs.
--
--   Differences from the source:
--   - encoding: a dataset P in a metric space (finite; a fractional solution with ‖y‖₁ ≥ 1 exists) → P a type with Fintype, Nonempty and MetricSpace instances; reason: the dataset is a finite set of points; nonemptiness only excludes the empty dataset, which has no fractional solution
-- source:
--   Czumaj–Jiang–Jin–Lou–Wang, Fully Scalable MPC Algorithms for Euclidean Clustering, arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.8, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_RobustFracMP_mpRadius
import Definitions.Def_RobustFracMP_ball
import Definitions.Def_RobustFracMP_ring

set_option autoImplicit false

namespace RobustFracMP

/-- **Lemma 3.8 (additive smoothness of r^{(β)}).**

Czumaj–Jiang–Jin–Lou–Wang, *Fully Scalable MPC Algorithms for Euclidean Clustering*,
arXiv:2604.00954 (version of November 3, 2026; manuscript sha256 c65896fe…51d8), Lemma 3.8, p.16 (PDF p.18): "For any scale factor β > 0 and any two points p, q ∈ P,
r^{(β)}_p ≤ r^{(β)}_q + 2^{z−1} · β · dist^z(p, q) + 1/|B^{(β)}_q(r^{(β)}_q/2)| ·
( Σ_{t∈B^{(β)}_q(r^{(β)}_q/2)} (2^{z−1} − 1) · β · dist^z(t, q)
  + Σ_{t∈R^{(β)}_q(r^{(β)}_q/2)} (r^{(β)}_q − β · dist^z(t, q)) )."

**Formalization Note.** The ball `B^{(β)}_q(r^{(β)}_q/2)` contains `q`, so the denominator is at
least `1`. `dist t q` is written with `t` first, as printed. Standing hypotheses of Sections 2–3 (pp.10–14): `z ≥ 1` an integer, `(P, dist)` a finite
metric space (the dataset, with `F = P`), opening cost `λ > 0`; `r^{(β)}_p` is
`mpRadius z dist β lam p`, computed on the true metric (p.14). -/
theorem lemma_3_8 {P : Type*} [Fintype P] [Nonempty P] [MetricSpace P]
    (z : ℕ) (hz : 1 ≤ z) (lam : ℝ) (hlam : 0 < lam) (β : ℝ) (hβ : 0 < β) (p q : P) :
    mpRadius z dist β lam p ≤
      mpRadius z dist β lam q + 2 ^ (z - 1) * β * dist p q ^ z +
        1 / ((ball z β q (mpRadius z dist β lam q / 2)).card : ℝ) *
          (∑ t ∈ ball z β q (mpRadius z dist β lam q / 2), (2 ^ (z - 1) - 1) * β * dist t q ^ z +
            ∑ t ∈ ring z β q (mpRadius z dist β lam q / 2),
              (mpRadius z dist β lam q - β * dist t q ^ z)) := by sorry

end RobustFracMP
