-- Prove2me | Theorems.Thm_TwistedUnipotentTerm_wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem
-- name    : TwistedUnipotentTerm.wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/bfe9a856-03ca-56cb-b005-6848fe7c44cc
-- title:
--   Bi-invariance of the word indicator under semi-local integral units
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, let $v$ be a height one prime of $\mathcal{O}_K$ and let $w$ be an extension of $v$ to $\mathcal{O}_L$, i.e. a height one prime of $\mathcal{O}_L$ lying under $v$; write $L_w$ for the $w$-adic completion of $L$ and $U_w \le \mathrm{GL}_2(L_w)$ for the image of $\mathrm{GL}_2(\mathcal{O}_w) \to \mathrm{GL}_2(L_w)$ induced by the structure map of $\mathcal{O}_w =$ the $w$-adic integers. Let $g \in \mathrm{GL}_2(L_w)$, let $n \in \mathbb{N}$ and let $rT : \mathrm{Fin}\,n \to \mathrm{GL}_2(L_w)$ satisfy `IsHeckeCosetSystem` for $U_w$ and $g$: every $rT(i)$ lies in the double coset $U_w\,g\,U_w$, every element of that double coset has the same image as some $rT(i)$ in $\mathrm{GL}_2(L_w)/U_w$, and $i \mapsto rT(i)U_w$ is injective. Let $z \in \mathrm{GL}_2(L_w)$ commute with every element of $\mathrm{GL}_2(L_w)$, and let $k, j \in \mathbb{N}$. Let $S =$ [`AutomorphicForm.semiLocalIntegralSet K L v`](def/AutomorphicForm_TwistedOrbital.html#L136) be the set of those $u \in \mathrm{GL}_2(L \otimes_K K_v)$ for which both $u$ and $u^{-1}$ have all entries in the image of the integral tensor map, and recall that the word indicator is $$W_{k,j}(x) = \sum_{\iota : \mathrm{Fin}\,k \to \mathrm{Fin}\,n} \mathbf{1}_S\bigl(\sigma(\lambda(rT(\iota(0))\cdots rT(\iota(k-1))\,z^{j}))^{-1} x\bigr),$$ where $\lambda$ is the embedding [`AdelicDock.localEmbed`](def/AdelicDock_LocalEmbedding.html#L97) of $\mathrm{GL}_2(L_w)$ into $\mathrm{GL}_2$ of the finite adele ring of $L$ at $w$ and $\sigma$ is [`AutomorphicForm.semiLocalComponent`](def/AutomorphicForm_TwistedOrbital.html#L446) into $\mathrm{GL}_2(L \otimes_K K_v)$. Then for every $s \in S$ and every $x \in \mathrm{GL}_2(L \otimes_K K_v)$ one has $W_{k,j}(sx) = W_{k,j}(x)$ and $W_{k,j}(xs) = W_{k,j}(x)$.
--
--   This is the bi-invariance of the word indicator attached to a system of left coset representatives inside a Hecke double coset under the semi-local integral units at $v$, the elementary counterpart of the fact that characteristic functions of double cosets are bi-$U_w$-invariant. It feeds the analysis of the twisted unipotent orbital function, being used in the evaluation of that function as a multiple of a walk-counting indicator and in the proof that it is locally constant with compact support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TwistedUnipotentTerm_wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_LocalLanglands_HeckeCosetLocal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

theorem TwistedUnipotentTerm.wordIndicator_mul_eq_of_mem_semiLocalIntegralSet_of_isHeckeCosetSystem
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (g : GL (Fin 2) (w.1.adicCompletion L))
    (n : ℕ) (rT : Fin n → GL (Fin 2) (w.1.adicCompletion L))
    (hrT : HeckeIntegralSeam.IsHeckeCosetSystem
      (LocalGL2.integralSubgroup (w.1.adicCompletionIntegers L) (w.1.adicCompletion L)) g rT)
    (z : GL (Fin 2) (w.1.adicCompletion L)) (hz : ∀ y : GL (Fin 2) (w.1.adicCompletion L), z * y = y * z)
    (k j : ℕ) (s : GL (Fin 2) (L ⊗[K] v.adicCompletion K))
    (hs : s ∈ AutomorphicForm.semiLocalIntegralSet K L v)
    (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    TwistedUnipotentTerm.wordIndicator K L v w n rT z k j (s * x) =
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j x ∧
      TwistedUnipotentTerm.wordIndicator K L v w n rT z k j (x * s) =
        TwistedUnipotentTerm.wordIndicator K L v w n rT z k j x := by sorry
