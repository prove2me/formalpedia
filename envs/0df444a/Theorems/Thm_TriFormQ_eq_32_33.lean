-- Prove2me | Theorems.Thm_TriFormQ_eq_32_33
-- name    : TriFormQ.eq_32_33
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T21:46:52.079629+00:00
-- url     : https://prove2.me/theorems/cea1a0d2-b8f0-4183-92d5-eeb4bea57d25
-- title:
--   Section 6.3, Eqs. (32)–(33): a form vanishing on $S_U\times S_V\times S_W$ is determined by $a+b+c$ bilinear slices
-- statement:
--   Let $f$ be a trilinear form on $\mathbb F^n$ and let $S_U,S_V,S_W\le\mathbb F^n$ be subspaces with $f|_{S_U\times S_V\times S_W}\equiv 0$. Choose complements $\mathbb F^n=S_U\oplus L_U$, $\mathbb F^n=S_V\oplus L_V$, $\mathbb F^n=S_W\oplus L_W$ with bases $u_1,\dots,u_a$ of $L_U$, $v_1,\dots,v_b$ of $L_V$, $w_1,\dots,w_c$ of $L_W$ (so $a=\mathrm{codim}\,S_U$, etc.). Write $A_i=f(u_i,\cdot,\cdot)$, $B_j=f(\cdot,v_j,\cdot)$ and $C_k=f(\cdot,\cdot,w_k)$.
--
--   1. (Eq. (32)) If $u=u_0+\sum_i\alpha_iu_i$, $v=v_0+\sum_j\beta_jv_j$ and $w=w_0+\sum_k\gamma_kw_k$ with $u_0\in S_U$, $v_0\in S_V$, $w_0\in S_W$, then
--   $$f(u,v,w)=\sum_{i=1}^a\alpha_i A_i(v,w)+\sum_{j=1}^b\beta_j B_j(u_0,w)+\sum_{k=1}^c\gamma_k C_k(u_0,v_0).$$
--   2. (Eq. (33)) If $f'$ is another trilinear form that also vanishes on $S_U\times S_V\times S_W$, then $f'=f$ if and only if $f'$ and $f$ agree on the $a+b+c$ slices: $A_i$ on $\mathbb F^n\times\mathbb F^n$, $B_j$ on $S_U\times\mathbb F^n$, and $C_k$ on $S_U\times S_V$.
--
--   This is the structural fact that reduces identifying a low-analytic-rank trilinear form to identifying $O(\mathrm{AR}(f))$ matrices, one slice at a time.
--
--   Differences from the source:
--   - encoding: $f$ is completely determined by $a+b+c$ bilinear slices → Eq. (32) as an identity, and Eq. (33) as: for forms vanishing on $S_U\times S_V\times S_W$, equality iff agreement on the slices $A_i$ (on $V\times W$), $B_j$ (on $S_U\times W$), $C_k$ (on $S_U\times S_V$); reason: the two displays the section derives; Fig. 2 defines the slices' domains
--   - encoding: complements $L_U=\langle u_1,\dots,u_a\rangle$ with $a=\mathrm{codim}\,S_U$ → `IsCompl` complements with bases indexed by $\mathrm{Fin}\,a$, $\mathrm{Fin}\,b$, $\mathrm{Fin}\,c$; reason: a basis of a complement has $\mathrm{codim}$ elements
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Section 6.3, Eqs. (32)–(33), pp.34–35 (PDF pp.37–38)

import Definitions.Def_TriFormQ_TriForm_eval

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Section 6.3, Eqs. (32)–(33),
pp.34–35 (PDF pp.37–38): "Let f : U × V × W → 𝔽_q be trilinear. Suppose that there exist
subspaces S_U ≤ U, S_V ≤ V, S_W ≤ W such that f|_{S_U×S_V×S_W} = 0. Denoting a = codim(S_U),
b = codim(S_V), c = codim(S_W), then f is commpletely determined by a + b + c bilinear slices";
with complements `U = S_U ⊕ L_U`, `L_U = ⟨u₁, …, u_a⟩` (and likewise for V, W),
`u = u₀ + Σ αᵢuᵢ`, `v = v₀ + Σ βⱼvⱼ`, `w = w₀ + Σ γₖwₖ`, Eq. (32):
`f(u, v, w) = Σᵢ αᵢ Aᵢ(v, w) + Σⱼ βⱼ Bⱼ(u₀, w) + Σₖ γₖ Cₖ(u₀, v₀)`, where (Fig. 2)
`Aᵢ = f(uᵢ, ·, ·)` on `V × W`, `Bⱼ = f(·, vⱼ, ·)` on `S_U × W`, `Cₖ = f(·, ·, wₖ)` on `S_U × S_V`;
and Eq. (33): a candidate that also vanishes on `S_U × S_V × S_W` equals `f` iff it agrees with
`f` on these `a + b + c` slices.

**Formalization Note.** `L_U, L_V, L_W` are complements (`IsCompl`) with bases indexed by
`Fin a`, `Fin b`, `Fin c` (so `a = codim S_U` etc.). Clause (i) is Eq. (32); clause (ii) is Eq. (33): a
form `θ'` that also vanishes on `S_U × S_V × S_W` equals `θ` (as coefficient tensors) if and only
if the two agree on the `a + b + c` slices. -/
theorem eq_32_33 {F : Type} [Field F] {n : ℕ} (θ : TriForm F n)
    (SU SV SW LU LV LW : Submodule F (Vec F n)) (hU : IsCompl SU LU) (hV : IsCompl SV LV)
    (hW : IsCompl SW LW) {a b c : ℕ} (bU : Module.Basis (Fin a) F LU)
    (bV : Module.Basis (Fin b) F LV) (bW : Module.Basis (Fin c) F LW)
    (hθ : ∀ u ∈ SU, ∀ v ∈ SV, ∀ w ∈ SW, TriForm.eval θ u v w = 0) :
    (∀ (u v w u₀ v₀ w₀ : Vec F n) (α : Fin a → F) (β : Fin b → F) (γ : Fin c → F),
      u₀ ∈ SU → v₀ ∈ SV → w₀ ∈ SW →
      u = u₀ + ∑ i, α i • (bU i : Vec F n) →
      v = v₀ + ∑ j, β j • (bV j : Vec F n) →
      w = w₀ + ∑ k, γ k • (bW k : Vec F n) →
      TriForm.eval θ u v w =
        ∑ i, α i * TriForm.eval θ (bU i) v w + ∑ j, β j * TriForm.eval θ u₀ (bV j) w +
          ∑ k, γ k * TriForm.eval θ u₀ v₀ (bW k)) ∧
    (∀ θ' : TriForm F n, (∀ u ∈ SU, ∀ v ∈ SV, ∀ w ∈ SW, TriForm.eval θ' u v w = 0) →
      (θ' = θ ↔
        (∀ i v w, TriForm.eval θ' (bU i) v w = TriForm.eval θ (bU i) v w) ∧
        (∀ j, ∀ u₀ ∈ SU, ∀ w, TriForm.eval θ' u₀ (bV j) w = TriForm.eval θ u₀ (bV j) w) ∧
        (∀ k, ∀ u₀ ∈ SU, ∀ v₀ ∈ SV,
          TriForm.eval θ' u₀ v₀ (bW k) = TriForm.eval θ u₀ v₀ (bW k)))) := by sorry

end TriFormQ
