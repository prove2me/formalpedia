-- Prove2me | Theorems.Thm_OuterplanarL1Tan_Linear_exists_facialReparam_of_exteriorParam
-- name    : OuterplanarL1Tan.Linear.exists_facialReparam_of_exteriorParam
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T20:59:28.971195+00:00
-- url     : https://prove2.me/theorems/b9e24d07-4d92-4899-9ff9-e8ba9f0697d9
-- title:
--   The boundary of an exterior parametrisation traverses the outer facial walk
-- statement:
--   Let $G$ be a connected simple graph on a finite vertex type $V$ with at least two vertices, and $D$ a plane drawing of $G$ (`PlaneDrawing G`). Let $O$ be its outer face and $\partial O$ the frontier of $O$. Suppose $F : \mathbb R \times \mathbb R \to \mathbb R^2$, written $F(r, t)$, is continuous on $\{r \ge 0\}$, $1$-periodic in $t$, injective on $\{r > 0,\ 0 \le t < 1\}$, maps $\{r > 0\}$ onto $O$, maps the line $r = 0$ onto $\partial O$, and has $t \mapsto F(0, t)$ constant on no interval of positive length.
--
--   Then there are $m > 0$, vertices $u_0, \dots, u_{m-1}$, and $\tau : \mathbb R \to \mathbb R$, continuous and strictly increasing on $[0, 1]$ with $\tau(1) = \tau(0) + 1$, such that:
--
--   - $\{u_j\}$ is exactly the set of vertices whose point lies in the closure of $O$;
--   - each step $u_j \to u_{j+1 \bmod m}$ is an edge of $G$;
--   - no directed step occurs twice;
--   - for every $j$ and every $s \in [0,1]$, $F\bigl(0, \tau((j+s)/m)\bigr)$ is the point at parameter $s$ of the drawing's arc from $u_j$ to $u_{j+1 \bmod m}$.
--
--   In words, the boundary curve of an exterior parametrisation, suitably reparametrised, traverses the outer facial walk with one edge arc per step, so it fixes the cyclic order of the boundary vertices.
--
--   `ConformalBoundary.caratheodory_torhorst_exterior` gives such an $F$, namely $F(r, t) = \Phi\bigl((1+r)e^{2\pi i t}\bigr)$. With that $F$, `OuterplanarL1Tan.Linear.exists_outerFacialWalk_of_connected` follows from this statement: the collar is $F(r, \tau(t))$. Tan's paper uses the cyclic boundary order without proof (§2.1, printed p. 2: "let $b_1, \dots, b_m$ be the vertices lying on the outer face in this order").
-- source:
--   Zihan Tan, Improved Embedding of k-Outerplanar Metrics into ℓ1, ACM STOC 2027 submission 262, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/262.pdf, p. 2, §2.1 (PDF p. 3), "let b₁, …, bₘ be the vertices lying on the outer face in this order"

import Definitions.Def_OuterplanarL1Tan_Linear_PlaneGeometry

open OuterplanarL1Tan.Linear in
theorem OuterplanarL1Tan.Linear.exists_facialReparam_of_exteriorParam {V : Type} [Fintype V]
    {G : SimpleGraph V} (connected : G.Connected) (D : PlaneDrawing G)
    (nontrivial : ∃ v w : V, v ≠ w) (F : ℝ → ℝ → Plane)
    (continuous : ContinuousOn (Function.uncurry F) (Set.Ici 0 ×ˢ Set.univ))
    (periodic : ∀ r t, F r (t + 1) = F r t)
    (injective : Set.InjOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ico 0 1))
    (onto : Function.uncurry F '' (Set.Ioi 0 ×ˢ Set.univ) = D.outerFace Set.univ)
    (boundary : Set.range (F 0) = frontier (D.outerFace Set.univ))
    (light : ∀ α β : ℝ, α < β → ∃ θ ∈ Set.Icc α β, F 0 θ ≠ F 0 α) :
    ∃ (m : ℕ) (hm : 0 < m) (u : Fin m → V) (τ : ℝ → ℝ),
      Set.range u = D.boundary Set.univ ∧
      (∀ j, G.Adj (u j) (u (cyclicNext hm j))) ∧
      (∀ i j, u i = u j → u (cyclicNext hm i) = u (cyclicNext hm j) → i = j) ∧
      ContinuousOn τ (Set.Icc 0 1) ∧ StrictMonoOn τ (Set.Icc 0 1) ∧ τ 1 = τ 0 + 1 ∧
      ∀ j (h : G.Adj (u j) (u (cyclicNext hm j))) (s : unitInterval),
        F 0 (τ (((j.val : ℝ) + (s : ℝ)) / (m : ℝ))) = D.arc h s := by sorry
