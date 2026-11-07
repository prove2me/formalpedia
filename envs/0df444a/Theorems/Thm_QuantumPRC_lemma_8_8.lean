-- Prove2me | Theorems.Thm_QuantumPRC_lemma_8_8
-- name    : QuantumPRC.lemma_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:36:16.735194+00:00
-- url     : https://prove2.me/theorems/ec3302e1-53ac-4f91-8573-31ed05c72c77
-- title:
--   Lemma 8.8 — score properties of BlockRecover on a good graph
-- statement:
--   Let $t,d$ be positive integers and let $G$ be $(t,d)$-good for $v\in\{0,1\}^{2n}$, with biadjacency matrix $B$. Let $u\in\{0,1\}^{2n}$, $e=v\oplus Au$, and let $\hat u\in\{0,1\}^n$ be any estimate of $u_R$. Put $z=u_R\oplus\hat u$, the residual $r=e_L\oplus B\hat u$, and the scores $\sigma(j)=|\{i\in[n] : B_{i,j}=1,\ r_i=1\}|$. Then
--
--   1. (stopping at the correct estimate) if $z=0$, then $\sigma(j)\le d/16$ for every $j\in[n]$;
--   2. (existence of a candidate) if $0<\mathrm{wt}(z)\le 2t$, then $\max_j\sigma(j)>5d/8$;
--   3. (decrease in signal weight) for every $j$ with $\sigma(j)>5d/8$,
--   $$
--   \mathrm{wt}\big(B(z\oplus\varepsilon_j)\big)-\mathrm{wt}(Bz)<-d/8 .
--   $$
--
--   The same three properties hold for the right block, with $(B,u_R,v_L)$ replaced by $(B^\top,u_L,v_R)$: $z=u_L\oplus\hat u$, $r=e_R\oplus B^\top\hat u$. These are the three facts from which the correctness of Recover (Theorem 8.9) follows.
--
--   Differences from the source:
--   - generalization: the k-th estimate û_R^(k) of BlockRecover and its residual r_L^(k) = e_L ⊕ Bû_R^(k) → an arbitrary estimate û with residual e_L ⊕ Bû; reason: the iterates of the algorithm are special cases; the paper's proof uses only the residual identity r = Bz ⊕ v_L, which holds for every û
--   - encoding: σ_k(j) ≤ d/16, > 5d/8, < −d/8 → 16σ ≤ d, 5d < 8σ, 8·(difference) < −d; reason: denominators cleared; same inequalities
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Lemma 8.8, p.56; Definitions 8.1–8.3, p.54; Construction 8.5, p.55

import Mathlib
import Definitions.Def_QuantumPRC_recover

namespace QuantumPRC

/-- **Lemma 8.8** (score properties). Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…), Lemma 8.8,
p.56: "Assume that `G` is `(t, d)`-good for `v`. For the left block, set `M = B`, `x̂^{(k)} = û_R^{(k)}`, and
`r^{(k)} = r_L^{(k)}`. Let `z_R^{(k)} = u_R ⊕ û_R^{(k)}` denote the estimation error after `k` flips. The
residual is `r_L^{(k)} = e_L ⊕ Bû_R^{(k)} = Bz_R^{(k)} ⊕ v_L`. (i) Stopping at the correct estimate. If
`z_R^{(k)} = 0`, then `σ_k(j) ≤ d/16` for every `j ∈ [n]`. (ii) Existence of a candidate. If
`0 < wt(z_R^{(k)}) ≤ 2t`, then `max_{j∈[n]} σ_k(j) > 5d/8`. (iii) Decrease in signal weight. For every
`j ∈ [n]`, if `σ_k(j) > 5d/8`, then `wt(B(z_R^{(k)} ⊕ ε_j)) − wt(Bz_R^{(k)}) < −d/8`. The same three
properties hold for the right block after replacing `(B, u_R, v_L)` with `(B⊤, u_L, v_R)`."

**Formalization Note.** `e = v ⊕ Au`; the estimate `û` (the paper's `û^{(k)}`) is arbitrary, the
residual is `r = e_L ⊕ Bû` and the score is `σ(j) = score B r j` (Eq. (196)); the bounds are cleared
of denominators. `t, d` are positive, as in Definition 8.3. -/
theorem lemma_8_8 {n t d : ℕ} (ht : 0 < t) (hd : 0 < d) (G : SimpleGraph (Fin (2 * n)))
    [DecidableRel G.Adj] (v : Bits (2 * n)) (hG : IsGood t d v G) (u : Bits (2 * n)) :
    let e := xorB v (adjMul G u)
    let B : Fin n → Fin n → Bool := biadj G
    let Bt : Fin n → Fin n → Bool := fun y x => biadj G x y
    (∀ uh : Bits n,
      let z := xorB (fun j => u (vR j)) uh
      let res := xorB (fun i => e (vL i)) (bmv B uh)
      (z = (fun _ => false) → ∀ j, 16 * score B res j ≤ d) ∧
      (0 < wt z → wt z ≤ 2 * t → ∃ j, 5 * d < 8 * score B res j) ∧
      (∀ j, 5 * d < 8 * score B res j →
        8 * ((wt (bmv B (xorB z (unitVec j))) : ℤ) - wt (bmv B z)) < -(d : ℤ))) ∧
    (∀ uh : Bits n,
      let z := xorB (fun i => u (vL i)) uh
      let res := xorB (fun j => e (vR j)) (bmv Bt uh)
      (z = (fun _ => false) → ∀ j, 16 * score Bt res j ≤ d) ∧
      (0 < wt z → wt z ≤ 2 * t → ∃ j, 5 * d < 8 * score Bt res j) ∧
      (∀ j, 5 * d < 8 * score Bt res j →
        8 * ((wt (bmv Bt (xorB z (unitVec j))) : ℤ) - wt (bmv Bt z)) < -(d : ℤ))) := by sorry

end QuantumPRC
