-- Prove2me | Theorems.Thm_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem
-- name    : TateModule.exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/be77b810-2eed-5c69-b035-48a3ef4cb827
-- title:
--   Homomorphisms from a saturated Tate submodule and its first projection
-- statement:
--   Let $p$ be a prime and $M$ an abelian group, and let $T =$ [`TateModule p M`](def/EllipticCurve_TateModule.html#L15) be the additive group of sequences $x : \mathbb{N} \to M$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, with [`TateModule.proj p M n`](def/EllipticCurve_TateModule.html#L122) the evaluation $x \mapsto x_n$, an additive map $T \to M$. Let $P$ be a $\mathbb{Z}_p$-submodule of $T$ which is saturated in the sense that $p\,x \in P$ implies $x \in P$ for every $x \in T$, and let $N$ be an abelian group with $p\,y = 0$ for all $y \in N$. The assertion is that there is an isomorphism of additive groups $\rho$ from $\operatorname{Hom}(P, N)$ onto $\operatorname{Hom}(A, N)$, where $A \le M$ is the image of the additive subgroup underlying $P$ under evaluation at index $1$, with two properties: first, for every $\varphi : P \to N$, every $x \in P$ and every $a \in A$ with $a = x_1$, one has $\rho(\varphi)(a) = \varphi(x)$; second, for every $\mathbb{Z}_p$-linear endomorphism $T'$ of $T$ and every additive endomorphism $t$ of $M$ with $(T'x)_1 = t(x_1)$ for all $x \in T$ and $T'(P) \subseteq P$, and for all $\varphi$ and all $a, a' \in A$ with $a' = t(a)$, one has $\rho(\varphi \circ T'|_P)(a) = \rho(\varphi)(a')$.
--
--   This is the standard identification $\operatorname{Hom}(P,N) \cong \operatorname{Hom}(\mathrm{proj}_1(P),N)$ for $pN = 0$: a homomorphism into a group killed by $p$ factors through $P/pP$, and for saturated $P$ the first-level projection realises this quotient, the second clause recording compatibility with operators acting on the tower and on $M$ simultaneously. It is used in the study of $p$-adic torus coordinates and polarised differentials on modular curves, where the operators in question are Hecke and Galois operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TateModule_exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem.lean

import Mathlib
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem TateModule.exists_addEquiv_addMonoidHom_map_proj_one_of_forall_smul_mem
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (P : Submodule ℤ_[p] ↥(TateModule p M))
    (hsat : ∀ x : ↥(TateModule p M), (p : ℤ_[p]) • x ∈ P → x ∈ P)
    (N : Type*) [AddCommGroup N] (hN : ∀ y : N, p • y = 0) :
    ∃ ρ : (↥P →+ N) ≃+ (↥((P.toAddSubgroup).map (TateModule.proj p M 1)) →+ N),
      (∀ (φ : ↥P →+ N) (x : ↥P) (a : ↥((P.toAddSubgroup).map (TateModule.proj p M 1))),
        (a : M) = TateModule.proj p M 1 (x : ↥(TateModule p M)) → ρ φ a = φ x) ∧
      (∀ (T : ↥(TateModule p M) →ₗ[ℤ_[p]] ↥(TateModule p M)) (t : M →+ M)
        (hTt : ∀ x : ↥(TateModule p M), TateModule.proj p M 1 (T x) = t (TateModule.proj p M 1 x))
        (hTP : ∀ x ∈ P, T x ∈ P)
        (φ : ↥P →+ N) (a a' : ↥((P.toAddSubgroup).map (TateModule.proj p M 1))),
        (a' : M) = t (a : M) → ρ (φ.comp (T.restrict hTP).toAddMonoidHom) a = ρ φ a') := by sorry
