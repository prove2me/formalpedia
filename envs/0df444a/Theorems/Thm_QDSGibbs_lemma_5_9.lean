-- Prove2me | Theorems.Thm_QDSGibbs_lemma_5_9
-- name    : QDSGibbs.lemma_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:39:29.942039+00:00
-- url     : https://prove2.me/theorems/fc5cc1ac-8113-4f68-8523-6d66ab6acd5e
-- title:
--   Lemma 5.9 — from interval covariances to a joint boundary marginal
-- statement:
--   Let $B$ be an interval of a nearest-neighbour chain with local dimensions $2\le d_i\le d$, $\beta>0$, and suppose $\sigma^B_\beta$ satisfies the interval covariance bound (5.18) with a constant $C_{\mathrm{cl}}\ge0$ and a nonnegative nonincreasing profile $f$. Let $A,D,C\subseteq B$ be intervals in this left-to-right order, either end interval allowed to be empty. If $D$ is at distance at least $v$ from both nonempty end intervals, then
--
--   $$
--   \big\|(\sigma^B_\beta)_{A\cup C\cup D}-(\sigma^B_\beta)_{A\cup C}\otimes(\sigma^B_\beta)_D\big\|_1\le3C_{\mathrm{cl}}d^{2(|A|+|C|)}f(v).
--   $$
--
--   Differences from the source:
--   - encoding: sites $1,\dots,N$, bonds $W_i$ on $\{i,i+1\}$ → 0-based sites `Fin N`, bond `b : Fin (N−1)` on $\{b,b+1\}$; reason: a relabelling
--   - encoding: operators on a region $U$, partial traces $\mathrm{Tr}_S$, marginals and restricted Gibbs states acting on the subsystem → full-space matrices on $\prod_i \mathrm{Fin}\,d_i$: $A\otimes\mathbb 1$, `ptr S X` $=\mathbb 1_S\otimes\mathrm{Tr}_S X$, `gibbs β (hamOn I Ω)` $=\sigma^\Omega_\beta\otimes\mathbb 1/\dim$; reason: the paper extends operators by the identity in full-system expressions (p.10); norms, traces of products and covariances are unchanged
--   - reading: "a nonincreasing profile $f$" and the numerical constant $C_{\mathrm{cl}}$ of (5.18) → $f$ nonnegative and nonincreasing, $C_{\mathrm{cl}}\ge0$; reason: a covariance profile bounds absolute values and is nonnegative, as is the paper's $f(v)=e^{-c_{\mathrm{cl}}\sqrt v}$; the constant multiplies norms
--   - encoding: (5.18): $|\mathrm{Cov}|\le C_{\mathrm{cl}}\|A\|\|Y\|f(\mathrm{dist}(A,Y))$ → the bound with $f(v)$ for every $v$ not exceeding the distance between the supporting intervals (`ClusterBound`); reason: equivalent for nonincreasing $f$
-- source:
--   Rouzé–Stilck França, Rapid mixing of Gibbs samplers via quantum Dobrushin–Shlosman conditions, arXiv:2610.03578 (held file sha256 ede55815…), Lemma 5.9, p.45; (5.18), p.45

import Mathlib
import Definitions.Def_QDSGibbs_ClusterBound

open scoped Matrix

namespace QDSGibbs

/-- **Lemma 5.9 (From interval covariances to a joint boundary marginal)** (arXiv:2610.03578, held
file sha256 ede55815…, Lemma 5.9, p.45). Suppose `σ^B_β` satisfies (5.18) with a nonincreasing
profile `f`. Let `A, D, C ⊆ B` be intervals in this left-to-right order, with either end interval
allowed to be empty. If `D` is at distance at least `v` from both nonempty end intervals, then
`‖(σ^B_β)_{A∪C∪D} − (σ^B_β)_{A∪C} ⊗ (σ^B_β)_D‖₁ ≤ 3 C_cl d^{2(|A|+|C|)} f(v)` (5.19).

**Formalization Note** §5 setting: a chain with `2 ≤ d_i ≤ dmax` (`dmax` is the paper's `d`), `β > 0`,
`B` an interval. `σ^B_β` is the full-space `gibbs β (hamOn I B)`; marginals and the product of
marginals are in the full-space form `marg`/`margProd` (tensored with the normalized identity on the
rest), which has the same trace norm. A "profile" is a nonnegative nonincreasing `f`, and
`C_cl ≥ 0`. `D` is nonempty; an empty end interval imposes no distance condition (`DistGe` with an
empty set holds). The interval `D` of the paper is `Dm`. -/
theorem lemma_5_9 {N : ℕ} (hN : 1 ≤ N) (dmax : ℕ) (d : Fin N → ℕ) (hd : ∀ i, 2 ≤ d i ∧ d i ≤ dmax)
    (V : Fin N → Op d) (W : Fin (N - 1) → Op d) (hVW : IsChainHam V W) (β : ℝ) (hβ : 0 < β)
    (B : Finset (Fin N)) (hB : IsInterval B) (Ccl : ℝ) (hC : 0 ≤ Ccl) (f : ℝ → ℝ)
    (hf : Antitone f) (hf0 : ∀ v, 0 ≤ f v)
    (hcl : ClusterBound (gibbs β (hamOn (chain V W) B)) B Ccl f)
    (A Dm C : Finset (Fin N)) (hA : A = ∅ ∨ IsInterval A) (hCi : C = ∅ ∨ IsInterval C)
    (hD : IsInterval Dm) (hAB : A ⊆ B) (hCB : C ⊆ B) (hDB : Dm ⊆ B)
    (hAD : ∀ a ∈ A, ∀ x ∈ Dm, a < x) (hDC : ∀ x ∈ Dm, ∀ c ∈ C, x < c)
    (v : ℝ) (hvA : DistGe A Dm v) (hvC : DistGe Dm C v) :
    traceNorm (marg (A ∪ C ∪ Dm) (gibbs β (hamOn (chain V W) B)) -
        margProd (A ∪ C) Dm (gibbs β (hamOn (chain V W) B))) ≤
      3 * Ccl * (dmax : ℝ) ^ (2 * (A.card + C.card)) * f v := by sorry

end QDSGibbs
